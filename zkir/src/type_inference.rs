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

//! Static type inference over the IR instructions (the "types pass").

use std::collections::HashMap;

use anyhow::anyhow;
use midnight_zk_stdlib::ZkStdLibArch;

use crate::ir::{Identifier, Instruction as I, IrSource, Operand};
use crate::ir_instructions::to_bytes::to_bytes_offcircuit;
use crate::ir_types::{IrType, IrValue};

/// Memory of the types pass: the type of every variable defined so far, and
/// the chips required by the instructions processed so far.
struct TypeMemory {
    types: HashMap<Identifier, IrType>,
    arch: ZkStdLibArch,
}

impl TypeMemory {
    fn new(arch: ZkStdLibArch) -> Self {
        TypeMemory {
            types: HashMap::new(),
            arch,
        }
    }

    /// Binds `id` to type `t`, enabling the chip `t` lives on (if any).
    fn insert(&mut self, id: &Identifier, t: IrType) {
        use IrType::*;
        self.arch.jubjub |= matches!(t, JubjubPoint | JubjubScalar);
        self.arch.secp256k1 |= matches!(t, Secp256k1Point | Secp256k1Base | Secp256k1Scalar);
        self.arch.p256 |= matches!(t, Secp256r1Point | Secp256r1Base | Secp256r1Scalar);
        self.arch.curve25519 |= matches!(t, Curve25519Point | Curve25519Base | Curve25519Scalar);
        // Accumulators live on the in-circuit verifier.
        self.arch.bls12_381 |= matches!(t, Accumulator);
        self.arch.poseidon |= matches!(t, Accumulator);
        self.types.insert(id.clone(), t);
    }

    fn type_of(&self, operand: &Operand) -> Result<IrType, anyhow::Error> {
        match operand {
            Operand::Variable(id) => self
                .types
                .get(id)
                .cloned()
                .ok_or_else(|| anyhow!("variable not found: {:?}", id)),
            Operand::Immediate(_) => Ok(IrType::Native),
        }
    }

    /// Binds the outputs of `ins` to their types, enabling the chips that `ins`
    /// requires.
    fn infer(&mut self, ins: &I) -> Result<(), anyhow::Error> {
        match ins {
            I::Add { a, output, .. }
            | I::Mul { a, output, .. }
            | I::Neg { a, output }
            | I::Inv { a, output }
            | I::CondSelect { a, output, .. }
            | I::EcMul { a, output, .. }
            | I::Copy { val: a, output } => self.insert(output, self.type_of(a)?),

            I::Not { output, .. }
            | I::TestEq { output, .. }
            | I::ReconstituteField { output, .. }
            | I::LessThan { output, .. } => self.insert(output, IrType::Native),

            I::Encode { outputs, .. }
            | I::DivModPowerOfTwo { outputs, .. }
            | I::BytesIntoNatives { outputs, .. } => {
                for out_id in outputs {
                    self.insert(out_id, IrType::Native);
                }
            }

            I::Bytes32IntoLowHigh { outputs, .. } => {
                self.insert(&outputs.0, IrType::Native);
                self.insert(&outputs.1, IrType::Native);
            }

            I::And { output, .. } | I::Or { output, .. } | I::Xor { output, .. } => {
                self.insert(output, IrType::Bool)
            }

            I::PublicInput { val_t, output, .. }
            | I::PrivateInput { val_t, output, .. }
            | I::FromBytes { val_t, output, .. }
            | I::FromBytes32 { val_t, output, .. }
            | I::LoadConstant { val_t, output, .. } => self.insert(output, val_t.clone()),

            I::JubjubScalarFromNative { output, .. } => self.insert(output, IrType::JubjubScalar),

            I::TransientHash { output, .. } => {
                self.arch.poseidon = true;
                self.insert(output, IrType::Native);
            }
            I::PersistentHash { output, .. } => {
                self.arch.sha2_256 = true;
                self.insert(output, IrType::Bytes(32));
            }
            I::Keccak256 { output, .. } => {
                self.arch.keccak_256 = true;
                self.insert(output, IrType::Bytes(32));
            }
            I::Sha512 { output, .. } => {
                self.arch.sha2_512 = true;
                self.insert(output, IrType::Bytes(64));
            }
            I::HashToCurve { output, .. } => {
                self.arch.poseidon = true;
                self.insert(output, IrType::JubjubPoint);
            }

            I::EcMulGenerator { scalar, output } => {
                self.insert(output, self.type_of(scalar)?.point_of_scalar()?)
            }
            I::IntoCoordinates { point, outputs } => {
                let t = self.type_of(point)?.base_of_point()?;
                self.insert(&outputs.0, t.clone());
                self.insert(&outputs.1, t);
            }
            I::FromCoordinates { inputs, output } => {
                self.insert(output, self.type_of(&inputs.0)?.point_of_base()?)
            }

            I::ToBytes { input, output } => {
                let x = IrValue::default(&self.type_of(input)?);
                self.insert(output, to_bytes_offcircuit(&x)?.get_type());
            }
            I::IntoBytes32 { output, .. } | I::Bytes32FromLowHigh { output, .. } => {
                self.insert(output, IrType::Bytes(32))
            }
            I::Reverse { bytes, output } | I::ReverseBytes { bytes, output } => {
                self.insert(output, IrType::Bytes(self.type_of(bytes)?.byte_len()?))
            }
            I::Slice { len, output, .. } => self.insert(output, IrType::Bytes(*len)),
            I::BytesFromNatives { len, output, .. } => self.insert(output, IrType::Bytes(*len)),
            I::Nth { output, .. } => self.insert(output, IrType::Byte),
            I::Concat { inputs, output } => {
                let n = inputs
                    .iter()
                    .map(|op| self.type_of(op)?.byte_len())
                    .sum::<Result<u32, _>>()?;
                self.insert(output, IrType::Bytes(n));
            }

            I::PrepareVerification { output, .. } | I::Accumulate { output, .. } => {
                self.insert(output, IrType::Accumulator)
            }

            // The output of `InnerProof` is a proof, not an IR value.
            I::InnerProof { .. }
            | I::VerifyAccumulator { .. }
            | I::ConstrainEq { .. }
            | I::Assert { .. }
            | I::ConstrainToBoolean { .. }
            | I::ConstrainBits { .. }
            | I::Impact { .. }
            | I::Output { .. } => {}
        }
        Ok(())
    }
}

impl IrSource {
    /// Infers the type of every variable of the circuit and the chips it uses.
    ///
    /// This is not a type checker: the result is only meaningful for
    /// well-typed circuits, and ill-typed ones may or may not be rejected
    /// (they are rejected by [`IrSource::preprocess`] and the in-circuit pass).
    pub(crate) fn types_pass(
        &self,
    ) -> Result<(HashMap<Identifier, IrType>, ZkStdLibArch), anyhow::Error> {
        let mut mem = TypeMemory::new(ZkStdLibArch {
            poseidon: self.do_communications_commitment,
            nb_range_check_groups: 1,
            ..ZkStdLibArch::default()
        });

        for input_id in self.inputs.iter() {
            mem.insert(&input_id.name, input_id.val_t.clone());
        }

        for ins in self.instructions.iter() {
            mem.infer(ins)?;
        }

        Ok((mem.types, mem.arch))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use midnight_zk_stdlib::Relation;

    #[test]
    fn types_pass_enables_chips_of_intermediate_types() {
        // The curve types below only arise from instructions other than circuit
        // inputs, public/private inputs and from_bytes.
        let ir_raw = r#"{
           "version": { "major": 4, "minor": 0 },
           "inputs": [ { "name": "%x", "type": "Scalar<BLS12-381>" } ],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": [
               { "op": "load_constant", "type": "Scalar<Secp256k1>", "encoding": ["0x07", "0x00"], "output": "%k" },
               { "op": "ec_mul_generator", "scalar": "%k", "output": "%q" },
               { "op": "from_coordinates", "inputs": ["%x", "%x"], "output": "%p" },
               { "op": "keccak256", "alignment": [ { "tag": "atom", "value": { "tag": "bytes", "length": 1 } } ], "inputs": ["%x"], "output": "%h" }
           ]
        }"#;
        let ir = IrSource::load(ir_raw.as_bytes()).unwrap();
        let (_, arch) = ir.types_pass().unwrap();

        assert!(arch.secp256k1 && arch.jubjub && arch.keccak_256);
        assert!(!arch.p256 && !arch.curve25519);
        assert!(!arch.poseidon && !arch.sha2_256 && !arch.sha2_512);
        assert_eq!(arch, ir.used_chips());
    }
}
