// This file is part of midnight-ledger.
// Copyright (C) Midnight Foundation
// SPDX-License-Identifier: Apache-2.0
// Licensed under the Apache License, Version 2.0 (the "License");
// You may not use this file except in compliance with the License.
// You may obtain a copy of the License at
// http://www.apache.org/licenses/LICENSE-2.0
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use group::{Group, GroupEncoding};
use midnight_circuits::{
    CircuitField,
    instructions::{
        AssertionInstructions, AssignmentInstructions, DecompositionInstructions, EccInstructions,
        ZeroInstructions,
    },
    types::{AssignedByte, InnerValue},
};
use midnight_curves::{
    JubjubSubgroup,
    curve25519::{self, Curve25519Subgroup},
    k256, p256,
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk,
};
use midnight_zk_stdlib::ZkStdLib;
use num_bigint::BigUint;
use num_traits::Euclid;
use transient_crypto::curve::Fr;

use crate::{
    ir_instructions::{
        F,
        encode::jubjub_scalar_from_biguint,
        to_bytes::{jubjub_compress_incircuit, sec1_compress_incircuit, to_bytes_offcircuit},
    },
    ir_types::{CircuitValue, IrType, IrValue},
};

/// Builds (off-circuit) a value of the given type from a byte string.
///
/// Supported for the prime-field types:
///  - Native
///  - JubjubScalar
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// The bytes may have any length. They are interpreted as a little-endian
/// integer and reduced modulo the field order, so non-canonical encodings
/// are accepted.
///
///
/// Supported for the point types, as the inverse of the compressed encoding
/// of [`to_bytes_offcircuit`]. Unlike field elements, non-canonical encodings
/// of points are rejected, not reduced: the bytes must be exactly the
/// encoding of a point of that type.
///
/// # Errors
///
/// Errors if the input is not a supported type, or if the bytes are not the
/// canonical encoding of a point of that type.
pub fn from_bytes_offcircuit(val_t: &IrType, bytes: &[u8]) -> Result<IrValue, anyhow::Error> {
    // The deprecated `FromBytes32` instruction should only work for the output
    // types listed in `ir.rs`.
    use IrValue::*;

    let decoded = match val_t {
        IrType::Native => Ok(Native(Fr(from_le_bytes_with_reduction(bytes)))),

        IrType::JubjubScalar => Ok(JubjubScalar(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256k1Base => Ok(Secp256k1Base(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256k1Scalar => Ok(Secp256k1Scalar(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256r1Base => Ok(Secp256r1Base(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256r1Scalar => Ok(Secp256r1Scalar(from_le_bytes_with_reduction(bytes))),

        IrType::Curve25519Base => Ok(Curve25519Base(from_le_bytes_with_reduction(bytes))),

        IrType::Curve25519Scalar => Ok(Curve25519Scalar(from_le_bytes_with_reduction(bytes))),

        IrType::JubjubPoint => <&[u8; 32]>::try_from(bytes)
            .ok()
            .and_then(|b| Option::from(JubjubSubgroup::from_bytes(b)))
            .map(JubjubPoint)
            .ok_or_else(|| anyhow::anyhow!("Invalid {val_t:?} encoding")),

        IrType::Secp256k1Point => <[u8; 33]>::try_from(bytes)
            .ok()
            .and_then(|b| Option::from(k256::K256::from_bytes(&b.into())))
            .map(Secp256k1Point)
            .ok_or_else(|| anyhow::anyhow!("Invalid {val_t:?} encoding")),

        IrType::Secp256r1Point => <[u8; 33]>::try_from(bytes)
            .ok()
            .and_then(|b| Option::from(p256::P256::from_bytes(&b.into())))
            .map(Secp256r1Point)
            .ok_or_else(|| anyhow::anyhow!("Invalid {val_t:?} encoding")),

        IrType::Curve25519Point => <&[u8; 32]>::try_from(bytes)
            .ok()
            .and_then(|b| Option::from(curve25519::Curve25519::from_bytes(b)))
            .and_then(|p: curve25519::Curve25519| Curve25519Subgroup::from_edwards(p.0))
            .map(Curve25519Point)
            .ok_or_else(|| anyhow::anyhow!("Invalid {val_t:?} encoding")),

        _ => Err(anyhow::anyhow!("Unsupported from_bytes for type {val_t:?}",)),
    }?;

    // Field elements are reduced from bytes of any length, but points must be
    // given in canonical form.
    if val_t.is_point() {
        let re_encoded: Vec<u8> = to_bytes_offcircuit(&decoded)?.try_into()?;
        if re_encoded != bytes {
            return Err(anyhow::anyhow!(
                "The bytes of type {val_t:?} are not in canonical form: {bytes:?}"
            ));
        }
    }

    Ok(decoded)
}

/// Builds (in-circuit) a value of the given type from a byte string.
///
/// Supported for the prime-field types:
///  - Native
///  - JubjubScalar
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// The bytes may have any length. They are interpreted as a little-endian
/// integer and reduced modulo the field order, so non-canonical encodings
/// (integers not below the field order) are accepted.
///
/// Supported for the point types, as the inverse of the compressed encoding
/// of [`to_bytes_incircuit`](super::to_bytes::to_bytes_incircuit). Unlike
/// field elements, non-canonical encodings of points are rejected, not
/// reduced: the decoded point is witnessed, encoded again, and the result is
/// asserted equal to `bytes`.
///
/// # Errors
///
/// Errors if the input is not a supported type, or if the length of `bytes`
/// does not match the point type.
///
/// # Unsatisfiable Circuit
///
/// When `val_t` is a curve point type, if `bytes` are not the canonical
/// encoding of a point of that type.
pub fn from_bytes_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    val_t: &IrType,
    bytes: &[AssignedByte<F>],
) -> Result<CircuitValue, plonk::Error> {
    // The deprecated `FromBytes32` instruction should only work for the output
    // types listed in `ir.rs`.
    use CircuitValue::*;

    // On an invalid encoding, the decoded (witnessed) point defaults to the
    // generator instead of panicking; the circuit is then unsatisfiable.
    let values: Value<Vec<u8>> = bytes.iter().map(|b| b.value()).collect();

    match val_t {
        IrType::Native => std_lib.assigned_from_le_bytes(layouter, bytes).map(Native),

        IrType::JubjubScalar => {
            let x = std_lib.biguint().from_le_bytes(layouter, bytes)?;
            jubjub_scalar_from_biguint(std_lib, layouter, x).map(JubjubScalar)
        }

        IrType::Secp256k1Base => std_lib
            .secp256k1()
            .base_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Secp256k1Base),

        IrType::Secp256k1Scalar => std_lib
            .secp256k1()
            .scalar_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Secp256k1Scalar),

        IrType::Secp256r1Base => std_lib
            .p256()
            .base_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Secp256r1Base),

        IrType::Secp256r1Scalar => std_lib
            .p256()
            .scalar_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Secp256r1Scalar),

        IrType::Curve25519Base => std_lib
            .curve25519()
            .base_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Curve25519Base),

        IrType::Curve25519Scalar => std_lib
            .curve25519()
            .scalar_field_chip()
            .assigned_from_le_bytes(layouter, bytes)
            .map(Curve25519Scalar),

        IrType::JubjubPoint => {
            let value = values.map(|v| {
                <&[u8; 32]>::try_from(v.as_slice())
                    .ok()
                    .and_then(|b| Option::from(JubjubSubgroup::from_bytes(b)))
                    .unwrap_or(JubjubSubgroup::generator())
            });
            let curve = std_lib.jubjub();
            // `assign` constrains the point to the prime-order subgroup.
            let p = curve.assign(layouter, value)?;
            let (x, y) = (curve.x_coordinate(&p), curve.y_coordinate(&p));
            let encoding = jubjub_compress_incircuit(std_lib, layouter, &x, &y)?;
            assert_bytes_equal(std_lib, layouter, bytes, &encoding)?;
            Ok(JubjubPoint(p))
        }

        IrType::Secp256k1Point => {
            let value = values.map(|v| {
                <[u8; 33]>::try_from(v.as_slice())
                    .ok()
                    .and_then(|b| Option::from(k256::K256::from_bytes(&b.into())))
                    .unwrap_or(k256::K256::generator())
            });
            let curve = std_lib.secp256k1();
            let p = curve.assign(layouter, value)?;
            let is_id = curve.is_zero(layouter, &p)?;
            let (x, y) = (curve.x_coordinate(&p), curve.y_coordinate(&p));
            let encoding = sec1_compress_incircuit(
                std_lib,
                layouter,
                curve.base_field_chip(),
                &is_id,
                &x,
                &y,
            )?;
            assert_bytes_equal(std_lib, layouter, bytes, &encoding)?;
            Ok(Secp256k1Point(p))
        }

        IrType::Secp256r1Point => {
            let value = values.map(|v| {
                <[u8; 33]>::try_from(v.as_slice())
                    .ok()
                    .and_then(|b| Option::from(p256::P256::from_bytes(&b.into())))
                    .unwrap_or(p256::P256::generator())
            });
            let curve = std_lib.p256();
            let p = curve.assign(layouter, value)?;
            let is_id = curve.is_zero(layouter, &p)?;
            let (x, y) = (curve.x_coordinate(&p), curve.y_coordinate(&p));
            let encoding = sec1_compress_incircuit(
                std_lib,
                layouter,
                curve.base_field_chip(),
                &is_id,
                &x,
                &y,
            )?;
            assert_bytes_equal(std_lib, layouter, bytes, &encoding)?;
            Ok(Secp256r1Point(p))
        }

        IrType::Curve25519Point => {
            let bytes: &[AssignedByte<F>; 32] = bytes.try_into().map_err(|_| {
                plonk::Error::Synthesis(format!(
                    "from_bytes of {val_t:?} expects Bytes<32>, got Bytes<{}>",
                    bytes.len()
                ))
            })?;
            let value = values.map(|v| {
                <&[u8; 32]>::try_from(v.as_slice())
                    .ok()
                    .and_then(|b| Option::from(curve25519::Curve25519::from_bytes(b)))
                    .and_then(|p: curve25519::Curve25519| Curve25519Subgroup::from_edwards(p.0))
                    .unwrap_or(Curve25519Subgroup::generator())
            });
            std_lib
                .curve25519()
                .from_canonical_compressed_bytes(layouter, bytes, value)
                .map(Curve25519Point)
        }

        _ => Err(plonk::Error::Synthesis(format!(
            "Unsupported from_bytes for {val_t:?}",
        ))),
    }
}

// Asserts that `a` and `b` are equal, erroring if their lengths differ.
fn assert_bytes_equal(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    a: &[AssignedByte<F>],
    b: &[AssignedByte<F>],
) -> Result<(), plonk::Error> {
    if a.len() != b.len() {
        return Err(plonk::Error::Synthesis(format!(
            "expected Bytes<{}>, got Bytes<{}>",
            b.len(),
            a.len()
        )));
    }
    a.iter()
        .zip(b)
        .try_for_each(|(a, b)| std_lib.assert_equal(layouter, a, b))
}

/// Builds a prime field element from the given bytes by interpreting them
/// in little-endian as an integer. The integer can be bigger than field order.
pub(crate) fn from_le_bytes_with_reduction<F: CircuitField>(bytes: &[u8]) -> F {
    let (_, rem) = BigUint::from_bytes_le(bytes).div_rem_euclid(&F::modulus());
    let mut rem_bytes = rem.to_bytes_le();
    rem_bytes.resize(F::NUM_BYTES, 0);
    F::from_bytes_le(&rem_bytes).unwrap()
}

#[cfg(test)]
mod tests {
    use group::ff::Field;
    use midnight_curves::{Fr as JubjubFr, curve25519, k256, p256};
    use rand_chacha::rand_core::OsRng;
    use transient_crypto::curve::Fr;

    use super::*;

    // Starts from a random value, converts it into bytes (so as to obtain a
    // valid, canonical byte representation), then goes from those bytes
    // back into a value and into bytes again, checking that the
    // re-serialized bytes match the ones we started from.
    #[test]
    fn test_from_bytes_roundtrip() {
        use IrValue::*;

        let to_vec = |v: IrValue| -> Vec<u8> { <Vec<u8>>::try_from(v).unwrap() };

        for x in [
            Native(Fr(F::random(OsRng))),
            JubjubScalar(JubjubFr::random(OsRng)),
            Secp256k1Base(k256::Fp::random(OsRng)),
            Secp256k1Scalar(k256::Fq::random(OsRng)),
            Secp256r1Base(p256::Fp::random(OsRng)),
            Secp256r1Scalar(p256::Fq::random(OsRng)),
            Curve25519Base(curve25519::Fp::random(OsRng)),
            // Nb. dalek's inherent `Scalar::random` (which shadows
            // `ff::Field::random`) takes the rng by mutable reference.
            Curve25519Scalar(curve25519::Scalar::random(&mut OsRng)),
        ] {
            let val_t = x.get_type();
            let bytes = to_vec(to_bytes_offcircuit(&x).unwrap());
            assert_eq!(bytes.len(), 32);
            let y = from_bytes_offcircuit(&val_t, &bytes).unwrap();
            let bytes2 = to_vec(to_bytes_offcircuit(&y).unwrap());
            assert_eq!(bytes2, bytes, "{val_t:?}");
        }
    }

    // `from_bytes` accepts byte strings of any length; the bytes are
    // interpreted as a little-endian integer and reduced modulo the field
    // order. For inputs representing an integer below the field order,
    // `to_bytes . from_bytes` is the identity up to zero-padding to 32 bytes.
    #[test]
    fn test_from_bytes_arbitrary_length() {
        for val_t in [
            IrType::Native,
            IrType::JubjubScalar,
            IrType::Secp256k1Base,
            IrType::Secp256k1Scalar,
            IrType::Secp256r1Base,
            IrType::Secp256r1Scalar,
            IrType::Curve25519Base,
            IrType::Curve25519Scalar,
        ] {
            // Short input, below every field order: round-trips (padded).
            let short = [0x12u8, 0x34, 0x56];
            let x = from_bytes_offcircuit(&val_t, &short).unwrap();
            let bytes: Vec<u8> = to_bytes_offcircuit(&x).unwrap().try_into().unwrap();
            let mut expected = short.to_vec();
            expected.resize(32, 0);
            assert_eq!(bytes, expected, "{val_t:?}");

            // Wide input, above every field order: accepted and reduced.
            let wide = [0xffu8; 64];
            assert!(from_bytes_offcircuit(&val_t, &wide).is_ok(), "{val_t:?}");
        }
    }

    // Non-canonical (out-of-range) bytes are accepted and reduced modulo
    // each field's characteristic, rather than rejected.
    #[test]
    fn test_from_bytes_reduces_non_canonical_input() {
        let bytes = [0xffu8; 32];

        assert_eq!(
            from_bytes_offcircuit(&IrType::Native, &bytes).unwrap(),
            IrValue::Native(Fr(from_le_bytes_with_reduction(&bytes)))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::JubjubScalar, &bytes).unwrap(),
            IrValue::JubjubScalar(from_le_bytes_with_reduction(&bytes))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Secp256k1Base, &bytes).unwrap(),
            IrValue::Secp256k1Base(from_le_bytes_with_reduction(&bytes))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Secp256k1Scalar, &bytes).unwrap(),
            IrValue::Secp256k1Scalar(from_le_bytes_with_reduction(&bytes))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Secp256r1Base, &bytes).unwrap(),
            IrValue::Secp256r1Base(from_le_bytes_with_reduction(&bytes))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Secp256r1Scalar, &bytes).unwrap(),
            IrValue::Secp256r1Scalar(from_le_bytes_with_reduction(&bytes))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Curve25519Base, &bytes).unwrap(),
            IrValue::Curve25519Base(from_le_bytes_with_reduction(&bytes))
        );

        // Curve25519 scalars are built from 64 bytes (e.g. a SHA-512 digest,
        // as needed by ed25519), reduced modulo the group order.
        let wide = [0xffu8; 64];
        assert_eq!(
            from_bytes_offcircuit(&IrType::Curve25519Scalar, &wide).unwrap(),
            IrValue::Curve25519Scalar(from_le_bytes_with_reduction(&wide))
        );
        assert_eq!(
            from_bytes_offcircuit(&IrType::Curve25519Scalar, &wide).unwrap(),
            IrValue::Curve25519Scalar(curve25519::Scalar::from_bytes_mod_order_wide(&wide))
        );
    }

    // Non-field, non-point types are rejected.
    #[test]
    fn test_from_bytes_rejects_unsupported_types() {
        assert!(from_bytes_offcircuit(&IrType::Bytes(32), &[0u8; 32]).is_err());
        assert!(from_bytes_offcircuit(&IrType::Bool, &[0u8; 32]).is_err());
    }

    // Points must have exactly the length of their encoding, and invalid
    // encodings are rejected rather than reduced.
    #[test]
    fn test_from_bytes_rejects_invalid_point_encodings() {
        // Wrong length for the type.
        assert!(from_bytes_offcircuit(&IrType::Secp256k1Point, &[0u8; 32]).is_err());
        assert!(from_bytes_offcircuit(&IrType::Curve25519Point, &[0u8; 33]).is_err());
        assert!(from_bytes_offcircuit(&IrType::JubjubPoint, &[0u8; 31]).is_err());
        // Invalid SEC1 prefix.
        assert!(from_bytes_offcircuit(&IrType::Secp256r1Point, &[0xffu8; 33]).is_err());
        // Non-canonical `y` coordinate.
        assert!(from_bytes_offcircuit(&IrType::JubjubPoint, &[0xffu8; 32]).is_err());
        // Non-canonical encoding of the Jubjub identity (sign bit set on
        // `x = 0`), rejected as per ZIP 216.
        let mut id = [0u8; 32];
        id[0] = 1;
        id[31] = 0x80;
        assert!(from_bytes_offcircuit(&IrType::JubjubPoint, &id).is_err());
        // (0, -1) is a Jubjub point of order 2, outside the prime-order
        // subgroup.
        let minus_one: Vec<u8> = (-midnight_curves::Fq::ONE).to_bytes_le().to_vec();
        assert!(from_bytes_offcircuit(&IrType::JubjubPoint, &minus_one).is_err());
        // Non-canonical `y = p + 1` (for p = 2^255 - 19), which decompresses to
        // the Curve25519 identity.
        let mut p_plus_one = [0xffu8; 32];
        p_plus_one[0] = 0xee;
        p_plus_one[31] = 0x7f;
        assert!(from_bytes_offcircuit(&IrType::Curve25519Point, &p_plus_one).is_err());
    }
}
