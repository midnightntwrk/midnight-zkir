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

use midnight_circuits::{
    CircuitField, instructions::DecompositionInstructions, types::AssignedByte,
};

use midnight_proofs::{circuit::Layouter, plonk};
use midnight_zk_stdlib::ZkStdLib;
use num_bigint::BigUint;
use num_traits::Euclid;
use transient_crypto::curve::Fr;

use crate::{
    ir_instructions::F,
    ir_types::{CircuitValue, IrType, IrValue},
};

/// Builds (off-circuit) a value of the given type from a byte string of any
/// length. Supported for the prime-field types:
///  - Native
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// The bytes are interpreted as a little-endian integer and reduced modulo the
/// field order. In particular this allows building a `Curve25519Scalar` from
/// the 64-byte output of a 512-bit hash, as required by ed25519.
///
/// # Errors
///
/// Errors if the input is not a supported type.
pub fn from_bytes_offcircuit(val_t: &IrType, bytes: &[u8]) -> Result<IrValue, anyhow::Error> {
    use IrValue::*;

    match val_t {
        IrType::Native => Ok(Native(Fr(from_le_bytes_with_reduction(bytes)))),

        IrType::Secp256k1Base => Ok(Secp256k1Base(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256k1Scalar => Ok(Secp256k1Scalar(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256r1Base => Ok(Secp256r1Base(from_le_bytes_with_reduction(bytes))),

        IrType::Secp256r1Scalar => Ok(Secp256r1Scalar(from_le_bytes_with_reduction(bytes))),

        IrType::Curve25519Base => Ok(Curve25519Base(from_le_bytes_with_reduction(bytes))),

        IrType::Curve25519Scalar => Ok(Curve25519Scalar(from_le_bytes_with_reduction(bytes))),

        _ => Err(anyhow::anyhow!("Unsupported from_bytes for type {val_t:?}",)),
    }
}

/// Builds (in-circuit) a value of the given type from a byte string of any
/// length. Supported for the prime-field types:
///  - Native
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// The bytes are interpreted as a little-endian integer and reduced modulo the
/// field order. In particular this allows building a `Curve25519Scalar` from
/// the 64-byte output of a 512-bit hash, as required by ed25519.
///
/// # Errors
///
/// Errors if the input is not a supported type.
pub fn from_bytes_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    val_t: &IrType,
    bytes: &[AssignedByte<F>],
) -> Result<CircuitValue, plonk::Error> {
    use CircuitValue::*;

    match val_t {
        IrType::Native => std_lib.assigned_from_le_bytes(layouter, bytes).map(Native),

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

        _ => Err(plonk::Error::Synthesis(format!(
            "Unsupported from_bytes for {val_t:?}",
        ))),
    }
}

/// Fixed 32-byte wrappers around [`from_bytes_offcircuit`] and
/// [`from_bytes_incircuit`], preserving the pre-generalization API.
pub mod from_bytes32 {
    use super::*;

    /// Builds (off-circuit) a value of the given type from a 32-byte string,
    /// supporting the same prime-field types as [`from_bytes_offcircuit`].
    ///
    /// The bytes are interpreted as a little-endian integer and reduced modulo
    /// the field order.
    ///
    /// **Deprecated:** use [`from_bytes_offcircuit`] instead, which supports
    /// byte strings of any length.
    ///
    /// # Errors
    ///
    /// Errors if the input is not a supported type.
    pub fn from_bytes32_offcircuit(
        val_t: &IrType,
        bytes: &[u8; 32],
    ) -> Result<IrValue, anyhow::Error> {
        from_bytes_offcircuit(val_t, bytes)
    }

    /// Builds (in-circuit) a value of the given type from a 32-byte string,
    /// supporting the same prime-field types as [`from_bytes_incircuit`].
    ///
    /// The bytes are interpreted as a little-endian integer and reduced modulo
    /// the field order.
    ///
    /// **Deprecated:** use [`from_bytes_incircuit`] instead, which supports
    /// byte strings of any length.
    ///
    /// # Errors
    ///
    /// Errors if the input is not a supported type.
    pub fn from_bytes32_incircuit(
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<F>,
        val_t: &IrType,
        bytes: &[AssignedByte<F>; 32],
    ) -> Result<CircuitValue, plonk::Error> {
        from_bytes_incircuit(std_lib, layouter, val_t, bytes)
    }
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
    use midnight_curves::{curve25519, k256, p256};
    use rand_chacha::rand_core::OsRng;
    use transient_crypto::curve::Fr;

    use super::*;
    use crate::ir_instructions::to_bytes::to_bytes_offcircuit;

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

    // The 32-byte wrappers behave identically to the generic functions for
    // all supported prime-field types.
    #[test]
    fn test_from_bytes32_wrapper() {
        use from_bytes32::from_bytes32_offcircuit;

        let bytes = [0xffu8; 32];
        for val_t in [
            IrType::Native,
            IrType::Secp256k1Base,
            IrType::Secp256k1Scalar,
            IrType::Secp256r1Base,
            IrType::Secp256r1Scalar,
            IrType::Curve25519Base,
            IrType::Curve25519Scalar,
        ] {
            assert_eq!(
                from_bytes32_offcircuit(&val_t, &bytes).unwrap(),
                from_bytes_offcircuit(&val_t, &bytes).unwrap()
            );
        }
    }

    // Non-field types are rejected.
    #[test]
    fn test_from_bytes_rejects_unsupported_types() {
        assert!(from_bytes_offcircuit(&IrType::JubjubPoint, &[0u8; 32]).is_err());
        assert!(from_bytes_offcircuit(&IrType::Bytes(32), &[0u8; 32]).is_err());
        assert!(from_bytes_offcircuit(&IrType::Bool, &[0u8; 32]).is_err());
    }
}
