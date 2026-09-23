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

use group::GroupEncoding;
use midnight_circuits::{
    CircuitField,
    instructions::{
        ArithInstructions, AssertionInstructions, AssignmentInstructions, ControlFlowInstructions,
        ConversionInstructions, DecompositionInstructions, EccInstructions, ZeroInstructions,
    },
    types::{AssignedBit, AssignedByte, AssignedNative, InnerConstants, Instantiable},
};
use midnight_curves::curve25519;
use midnight_proofs::{circuit::Layouter, plonk};
use midnight_zk_stdlib::ZkStdLib;

use crate::{
    ir_instructions::F,
    ir_types::{CircuitValue, IrValue},
};

/// Converts (off-circuit) the given value into its fixed-size (32-byte)
/// representation. Supported on the prime-field types:
///  - Native
///  - JubjubScalar
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// In all the above prime fields, the byte representation is the little-endian
/// byte encoding of the underlying (canonical) integer. For inputs to
/// `from_bytes` representing an integer below the field order,
/// `to_bytes . from_bytes` is the identity up to zero-padding to 32 bytes.
///
/// Points are encoded in compressed form:
///  - `JubjubPoint` -> `Bytes(32)`, the little-endian `y` coordinate, 
///    with the least significant bit of `x` in the most significant bit 
///    of the last byte
///  - `Secp256k1Point`, `Secp256r1Point` -> `Bytes(33)`, SEC1 compressed
///    encoding, with the identity encoded as 33 zero bytes
///  - `Curve25519Point` -> `Bytes(32)`, ed25519 (RFC 8032) encoding
///
/// # Errors
///
/// Errors if the input is not a supported type.
pub fn to_bytes_offcircuit(value: &IrValue) -> Result<IrValue, anyhow::Error> {
    use IrValue::*;
    match value {
        Native(x) => Ok(Bytes(x.0.to_bytes_le().to_vec())),

        JubjubScalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256k1Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256k1Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256r1Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256r1Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Curve25519Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Curve25519Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Curve25519Point(p) => Ok(Bytes(curve25519::Curve25519::from(*p).to_bytes().to_vec())),

        JubjubPoint(p) => Ok(Bytes(p.to_bytes().to_vec())),

        Secp256k1Point(p) => Ok(Bytes(p.to_bytes().as_ref().to_vec())),

        Secp256r1Point(p) => Ok(Bytes(p.to_bytes().to_vec())),

        _ => Err(anyhow::anyhow!(
            "Unsupported to_bytes for {:?}",
            value.get_type(),
        )),
    }
}

/// Converts (in-circuit) the given value into its fixed-size (32-byte)
/// representation. Supported on the prime-field types:
///  - Native
///  - JubjubScalar
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// In all the above prime fields, the byte representation is the little-endian
/// byte encoding of the underlying (canonical) integer. Points are encoded in
/// compressed form. See [`to_bytes_offcircuit`].
///
/// # Errors
///
/// Errors if the input is not a supported type.
pub fn to_bytes_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    value: &CircuitValue,
) -> Result<CircuitValue, plonk::Error> {
    use CircuitValue::*;
    match value {
        Native(x) => std_lib
            .assigned_to_le_bytes(layouter, x, Some(32))
            .map(Bytes),

        JubjubScalar(s) => {
            let canonical = s.to_canonical_biguint(layouter, std_lib.biguint())?;
            let mut bytes = std_lib.biguint().to_le_bytes(layouter, &canonical)?;
            // The byte count follows the scalar's limb count rather than the
            // field size, so the encoding has to be cut or padded to 32 bytes.
            for byte in bytes.iter().skip(32) {
                std_lib.assert_equal_to_fixed(layouter, byte, 0u8)?;
            }
            bytes.resize(32, std_lib.assign_fixed(layouter, 0u8)?);

            Ok(Bytes(bytes))
        }

        Secp256k1Base(s) => std_lib
            .secp256k1()
            .base_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Secp256k1Scalar(s) => std_lib
            .secp256k1()
            .scalar_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Secp256r1Base(s) => std_lib
            .p256()
            .base_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Secp256r1Scalar(s) => std_lib
            .p256()
            .scalar_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Curve25519Base(s) => std_lib
            .curve25519()
            .base_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Curve25519Scalar(s) => std_lib
            .curve25519()
            .scalar_field_chip()
            .assigned_to_le_bytes(layouter, s, Some(32))
            .map(Bytes),

        Curve25519Point(p) => Ok(Bytes(
            std_lib
                .curve25519()
                .to_canonical_compressed_bytes(layouter, p)?
                .to_vec(),
        )),

        JubjubPoint(p) => {
            let curve = std_lib.jubjub();
            let (x, y) = (curve.x_coordinate(p), curve.y_coordinate(p));
            jubjub_compress_incircuit(std_lib, layouter, &x, &y).map(Bytes)
        }

        Secp256k1Point(p) => {
            let curve = std_lib.secp256k1();
            let is_id = curve.is_zero(layouter, p)?;
            let (x, y) = (curve.x_coordinate(p), curve.y_coordinate(p));
            sec1_compress_incircuit(std_lib, layouter, curve.base_field_chip(), &is_id, &x, &y)
                .map(Bytes)
        }

        Secp256r1Point(p) => {
            let curve = std_lib.p256();
            let is_id = curve.is_zero(layouter, p)?;
            let (x, y) = (curve.x_coordinate(p), curve.y_coordinate(p));
            sec1_compress_incircuit(std_lib, layouter, curve.base_field_chip(), &is_id, &x, &y)
                .map(Bytes)
        }

        _ => Err(plonk::Error::Synthesis(format!(
            "Unsupported to_bytes for {:?}",
            value.get_type(),
        ))),
    }
}

/// In-circuit compressed encoding of a Jubjub point given by its coordinates:
/// the little-endian `y` coordinate, with the least significant bit of `x` in
/// the most significant bit of the last byte.
pub(crate) fn jubjub_compress_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    x: &AssignedNative<F>,
    y: &AssignedNative<F>,
) -> Result<Vec<AssignedByte<F>>, plonk::Error> {
    // Decomposition into 32 (LE) bytes enforces canonicity.
    let mut y_bytes = std_lib.assigned_to_le_bytes(layouter, y, Some(32))?;
    let x_sign = std_lib.sgn0(layouter, x)?;

    // y < 2^255, so the most significant byte of y is at most 127 and adding
    // 128 causes no overflow.
    let last_byte = std_lib.linear_combination(
        layouter,
        &[
            (F::from(1), y_bytes[31].clone().into()),
            (F::from(128), x_sign.into()),
        ],
        F::from(0),
    )?;
    y_bytes[31] = std_lib.convert(layouter, &last_byte)?;
    Ok(y_bytes)
}

/// In-circuit SEC1 compressed encoding of a Weierstrass point given by its
/// identity flag and coordinates: `0x02 | (y mod 2)` followed by `x` in
/// big-endian, or 33 zero bytes for the identity.
///
/// The coordinates of the identity are unconstrained, so all bytes are
/// explicitly zeroed when `is_id` is set.
pub(crate) fn sec1_compress_incircuit<X, D: DecompositionInstructions<F, X>>(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    base_field_chip: &D,
    is_id: &AssignedBit<F>,
    x: &X,
    y: &X,
) -> Result<Vec<AssignedByte<F>>, plonk::Error>
where
    X: Instantiable<F> + InnerConstants + Clone,
    X::Element: CircuitField,
{
    let mut x_bytes = base_field_chip.assigned_to_le_bytes(layouter, x, Some(32))?;
    x_bytes.reverse();
    let y_sign = base_field_chip.sgn0(layouter, y)?;

    let prefix = std_lib.linear_combination(
        layouter,
        &[(F::from(1), y_sign.into())],
        F::from(2),
    )?;
    let prefix: AssignedByte<F> = std_lib.convert(layouter, &prefix)?;

    let zero: AssignedByte<F> = std_lib.assign_fixed(layouter, 0u8)?;
    std::iter::once(prefix)
        .chain(x_bytes)
        .map(|b| std_lib.select(layouter, is_id, &zero, &b))
        .collect()
}

#[cfg(test)]
mod tests {
    use group::{Group, ff::Field};
    use midnight_curves::{
        Fr as JubjubFr, JubjubAffine, JubjubExtended, JubjubSubgroup, curve25519, k256, p256,
    };
    use rand_chacha::rand_core::OsRng;
    use sha2::{Digest, Sha512};
    use transient_crypto::curve::Fr;

    use super::*;
    use crate::ir_instructions::from_bytes::from_bytes_offcircuit;

    #[test]
    fn test_to_bytes_roundtrip() {
        use IrValue::*;

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
            Curve25519Point(curve25519::Curve25519Subgroup::random(OsRng)),
            JubjubPoint(JubjubSubgroup::random(OsRng)),
            Secp256k1Point(k256::K256::random(OsRng)),
            Secp256r1Point(p256::P256::random(OsRng)),
            JubjubPoint(JubjubSubgroup::identity()),
            Secp256k1Point(k256::K256::identity()),
            Secp256r1Point(p256::P256::identity()),
        ] {
            let bytes: Vec<u8> = to_bytes_offcircuit(&x).unwrap().try_into().unwrap();
            assert_eq!(from_bytes_offcircuit(&x.get_type(), &bytes).unwrap(), x);
        }
    }

    fn to_vec(x: IrValue) -> Vec<u8> {
        to_bytes_offcircuit(&x).unwrap().try_into().unwrap()
    }

    #[test]
    fn test_to_bytes_point_known_vectors() {
        use IrValue::*;

        let mut expected = vec![0x58];
        expected.extend([0x66; 31]);
        assert_eq!(
            to_vec(Curve25519Point(curve25519::Curve25519Subgroup::generator())),
            expected
        );

        assert_eq!(
            hex::encode(to_vec(Secp256k1Point(k256::K256::generator()))),
            "0279be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798"
        );

        assert_eq!(
            hex::encode(to_vec(Secp256r1Point(p256::P256::generator()))),
            "036b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296"
        );

        for p in [
            Secp256k1Point(k256::K256::identity()),
            Secp256r1Point(p256::P256::identity()),
        ] {
            assert_eq!(to_vec(p), vec![0u8; 33]);
        }
    }

    // RFC 8032 §7.1, TEST 1.
    #[test]
    fn test_to_bytes_ed25519_public_key() {
        let sk = hex::decode("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60")
            .unwrap();
        let h = Sha512::digest(&sk);
        let mut s: [u8; 32] = h[..32].try_into().unwrap();
        s[0] &= 248;
        s[31] &= 127;
        s[31] |= 64;
        let s = curve25519::Scalar::from_bytes_mod_order(s);
        let pk = curve25519::Curve25519Subgroup::generator() * s;
        assert_eq!(
            hex::encode(to_vec(IrValue::Curve25519Point(pk))),
            "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
        );

        let p = curve25519::Curve25519Subgroup::random(OsRng);
        assert_eq!(
            to_vec(IrValue::Curve25519Point(p)),
            p.inner().compress().to_bytes()
        );
    }

    // Jubjub points use the same layout as Curve25519 points: little-endian
    // `y` (`v`), with the least significant bit of `x` (`u`) in the most
    // significant bit of the last byte.
    #[test]
    fn test_to_bytes_jubjub_layout() {
        for p in [
            JubjubSubgroup::generator(),
            JubjubSubgroup::identity(),
            JubjubSubgroup::random(OsRng),
        ] {
            let affine = JubjubAffine::from(JubjubExtended::from(p));
            let mut expected = affine.get_v().to_bytes_le().to_vec();
            expected[31] |= (affine.get_u().to_bytes_le()[0] & 1) << 7;
            assert_eq!(to_vec(IrValue::JubjubPoint(p)), expected);
        }
    }

    // Every supported field type serializes to exactly 32 bytes.
    #[test]
    fn test_to_bytes_output_is_32_bytes() {
        use IrValue::*;

        for x in [
            Native(Fr(F::random(OsRng))),
            JubjubScalar(JubjubFr::random(OsRng)),
            Secp256k1Base(k256::Fp::random(OsRng)),
            Secp256k1Scalar(k256::Fq::random(OsRng)),
            Secp256r1Base(p256::Fp::random(OsRng)),
            Secp256r1Scalar(p256::Fq::random(OsRng)),
            Curve25519Base(curve25519::Fp::random(OsRng)),
            Curve25519Scalar(curve25519::Scalar::random(&mut OsRng)),
        ] {
            let bytes: Vec<u8> = to_bytes_offcircuit(&x).unwrap().try_into().unwrap();
            assert_eq!(bytes.len(), 32);
        }
    }
}
