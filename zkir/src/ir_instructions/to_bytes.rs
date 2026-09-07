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

use midnight_circuits::{CircuitField, instructions::DecompositionInstructions};

use midnight_proofs::{circuit::Layouter, plonk};
use midnight_zk_stdlib::ZkStdLib;

use crate::{
    ir_instructions::F,
    ir_types::{CircuitValue, IrValue},
};

/// Converts (off-circuit) the given value into its fixed-size (32-byte)
/// representation. Supported on the prime-field types:
///  - Native
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
/// # Errors
///
/// Errors if the input is not a supported type.
pub fn to_bytes_offcircuit(value: &IrValue) -> Result<IrValue, anyhow::Error> {
    use IrValue::*;
    match value {
        Native(x) => Ok(Bytes(x.0.to_bytes_le().to_vec())),

        Secp256k1Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256k1Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256r1Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Secp256r1Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Curve25519Base(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        Curve25519Scalar(s) => Ok(Bytes(s.to_bytes_le().to_vec())),

        _ => Err(anyhow::anyhow!(
            "Unsupported to_bytes for {:?}",
            value.get_type(),
        )),
    }
}

/// Converts (in-circuit) the given value into its fixed-size (32-byte)
/// representation. Supported on the prime-field types:
///  - Native
///  - Secp256k1Base
///  - Secp256k1Scalar
///  - Secp256r1Base
///  - Secp256r1Scalar
///  - Curve25519Base
///  - Curve25519Scalar
///
/// In all the above prime fields, the byte representation is the little-endian
/// byte encoding of the underlying (canonical) integer; see
/// [`to_bytes_offcircuit`].
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

        _ => Err(plonk::Error::Synthesis(format!(
            "Unsupported to_bytes for {:?}",
            value.get_type(),
        ))),
    }
}

#[cfg(test)]
mod tests {
    use group::ff::Field;
    use midnight_curves::{curve25519, k256, p256};
    use rand_chacha::rand_core::OsRng;
    use transient_crypto::curve::Fr;

    use super::*;
    use crate::ir_instructions::from_bytes::from_bytes_offcircuit;

    #[test]
    fn test_to_bytes_roundtrip() {
        use IrValue::*;

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
            let bytes: Vec<u8> = to_bytes_offcircuit(&x).unwrap().try_into().unwrap();
            assert_eq!(from_bytes_offcircuit(&x.get_type(), &bytes).unwrap(), x);
        }
    }

    // Every supported field type serializes to exactly 32 bytes.
    #[test]
    fn test_to_bytes_output_is_32_bytes() {
        use IrValue::*;

        for x in [
            Native(Fr(F::random(OsRng))),
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
