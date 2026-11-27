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

//! Ledger proof conformance for depths 0 through 2 of `SequentialSource.agda`.

#[path = "../tests/common/verify_proof.rs"]
mod fixture;

use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_curves::Fq;
use midnight_proofs::utils::SerdeFormat;
use midnight_zk_stdlib::{KZG, prove, setup_pk, setup_vk};
use rand_chacha::ChaCha20Rng;
use sha2::{Digest, Sha256};
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{
    DeferredAccumulator, InnerProofWitness, ProofPreimage, Zkir, accumulator_pi_len,
};

use crate::ir::{Identifier, Instruction as I, IrMinorVersion, IrSource, Operand, TypedIdentifier};
use crate::ir_instructions::accumulate::accumulate_offcircuit;
use crate::ir_instructions::prepare_verification::prepare_verification_offcircuit;
use crate::ir_types::IrType;
use fixture::{preimage_with, srs, test_rng};

fn id(name: &str) -> Identifier {
    Identifier(name.into())
}

fn var(name: &str) -> Operand {
    Operand::Variable(id(name))
}

fn imm(value: u64) -> Operand {
    Operand::Immediate(Fr::from(value))
}

fn statement_operands(depth: usize, start: &str, finish: &str) -> impl Iterator<Item = Operand> {
    [var("%context"), var(start), var(finish)]
        .into_iter()
        .chain(std::iter::repeat_n(imm(0), depth))
}

fn source(depth: usize, child_key: Option<&[u8]>) -> IrSource {
    let mut ir = IrSource {
        version: IrMinorVersion::V0,
        inputs: vec![TypedIdentifier {
            name: id("%context"),
            val_t: IrType::Native,
        }],
        ..IrSource::default()
    };

    if depth == 0 {
        ir.instructions = vec![I::Impact {
            guard: imm(1),
            inputs: statement_operands(0, "%context", "%context").collect(),
        }]
        .into();
        return ir;
    }

    ir.inputs
        .extend(["%start", "%previous"].map(|name| TypedIdentifier {
            name: id(name),
            val_t: IrType::Native,
        }));
    let mut instructions = vec![
        I::Add {
            a: var("%previous"),
            b: imm(1),
            output: id("%finish"),
        },
        I::Impact {
            guard: imm(1),
            inputs: statement_operands(depth, "%start", "%finish").collect(),
        },
    ];

    let carried_fields = if depth > 1 {
        ir.inputs.insert(
            0,
            TypedIdentifier {
                name: id("%carried"),
                val_t: IrType::Accumulator,
            },
        );
        let fields: Vec<_> = (0..accumulator_pi_len())
            .map(|i| id(&format!("%a{i}")))
            .collect();
        instructions.push(I::Encode {
            input: var("%carried"),
            outputs: fields.clone(),
        });
        fields
    } else {
        vec![]
    };

    let child_key = child_key.expect("a nonzero depth pins its child key");
    instructions.extend([
        I::InnerProof {
            guard: imm(1),
            output: id("%proof"),
        },
        I::PrepareVerification {
            guard: imm(1),
            vk_hash: Sha256::digest(child_key).to_vec(),
            instance: carried_fields
                .into_iter()
                .map(Operand::Variable)
                .chain([imm(0)])
                .chain(statement_operands(depth - 1, "%start", "%previous"))
                .collect(),
            proof: id("%proof"),
            output: id("%opening"),
        },
    ]);
    let exposed = if depth > 1 {
        instructions.push(I::Accumulate {
            inputs: vec![var("%opening"), var("%carried")],
            output: id("%folded"),
        });
        var("%folded")
    } else {
        var("%opening")
    };
    instructions.push(I::VerifyAccumulator { input: exposed });
    ir.instructions = instructions.into();
    ir.inner_vks = vec![child_key.to_vec()];
    ir
}

fn instance(accumulators: &[DeferredAccumulator], statement: &[Fr]) -> Vec<Fq> {
    accumulators
        .iter()
        .flat_map(|acc| acc.as_public_input())
        .chain(statement.iter().map(|field| field.0))
        .collect()
}

fn prove_child(
    ir: &IrSource,
    preimage: &ProofPreimage,
    expected_instance: &[Fq],
    label: &str,
    rng: &mut ChaCha20Rng,
) -> (Vec<u8>, Vec<u8>) {
    let witness = ir.preprocess(preimage).expect("preprocess counter child");
    assert_eq!(witness.pis, expected_instance, "{label} instance");
    assert_eq!(witness.pi_skips, [None], "{label} skips");

    let k = ir.k();
    eprintln!("{label}: keygen and prove at k={k}");
    let params = srs().params_for(k);
    let vk = setup_vk::<_, KZG>(params.as_ref(), ir);
    let pk = setup_pk(ir, &vk);
    let mut key = Vec::new();
    vk.write(&mut key, SerdeFormat::Processed)
        .expect("write counter child key");
    let proof = prove::<_, PoseidonState<Fq>, KZG>(
        params.as_ref(),
        &pk,
        ir,
        &expected_instance.to_vec(),
        witness,
        rng,
    )
    .expect("prove counter child with Poseidon");
    (key, proof)
}

#[actix_rt::test]
#[ignore = "slow: proves two levels of in-circuit verification"]
async fn depth_two_counter_matches_sequential_source() {
    assert_eq!(accumulator_pi_len(), 12);
    let params = srs();
    let mut rng = test_rng();
    let context = Fr::from(42);
    let zero = Fr::from(0);
    let first = Fr::from(43);
    let second = Fr::from(44);

    let base = source(0, None);
    assert_eq!(base.accumulator_count(), 0);
    let base_statement = [zero, context, context, context];
    let mut base_preimage = preimage_with(vec![]);
    base_preimage.binding_input = zero;
    base_preimage.inputs = vec![context];
    base_preimage.public_transcript_inputs = base_statement[1..].to_vec();
    let base_instance = instance(&[], &base_statement);
    let (base_key, base_proof) =
        prove_child(&base, &base_preimage, &base_instance, "depth 0", &mut rng);

    let opening_one = prepare_verification_offcircuit(&base_key, &base_instance, &base_proof, true)
        .expect("prepare depth 0 proof");
    assert!(opening_one.check(&params.verifier));

    let step = source(1, Some(&base_key));
    assert_eq!(step.accumulator_count(), 1);
    let step_statement = [zero, context, context, first, zero];
    let step_instance = instance(&[opening_one], &step_statement);
    assert_eq!(step_instance.len(), 17);
    let mut step_preimage = preimage_with(vec![InnerProofWitness::Direct(base_proof)]);
    step_preimage.binding_input = zero;
    step_preimage.inputs = vec![context, context, context];
    step_preimage.public_transcript_inputs = step_statement[1..].to_vec();
    let (step_key, step_proof) =
        prove_child(&step, &step_preimage, &step_instance, "depth 1", &mut rng);

    let opening_two = prepare_verification_offcircuit(&step_key, &step_instance, &step_proof, true)
        .expect("prepare depth 1 proof with its full accumulator prefix");
    assert!(opening_two.check(&params.verifier));
    let folded = accumulate_offcircuit(&[opening_two, opening_one]).expect("fold both openings");
    assert!(folded.check(&params.verifier));

    let root = source(2, Some(&step_key));
    assert_eq!(root.accumulator_count(), 1);
    let root_statement = [zero, context, context, second, zero, zero];
    let mut root_preimage = preimage_with(vec![InnerProofWitness::Direct(step_proof)]);
    root_preimage.binding_input = zero;
    root_preimage.inputs = opening_one
        .as_public_input()
        .into_iter()
        .map(Fr)
        .chain([context, context, first])
        .collect();
    root_preimage.public_transcript_inputs = root_statement[1..].to_vec();
    let root_run = root.preprocess(&root_preimage).expect("preprocess depth 2");
    assert_eq!(root_run.pis.len(), 18);
    assert_eq!(root_run.pis, instance(&[folded], &root_statement));

    eprintln!("depth 2: keygen and prove");
    let (pk, vk) = root.keygen(params).await.expect("generate ledger keys");
    assert_eq!(vk.accumulators(), 1);
    let (proof, statement, skips) = root
        .prove(&mut rng, params, pk, &root_preimage)
        .await
        .expect("prove depth 2 with the ledger transcript");
    assert_eq!(proof.accumulators, [folded]);
    assert_eq!(statement, root_statement);
    assert_eq!(skips, [None]);
    vk.verify(&params.verifier, &proof, statement.iter().copied())
        .expect("verify depth 2 and its folded pairing");

    for (index, label) in [(1, "context"), (2, "start"), (3, "finish")] {
        let mut changed = root_statement;
        changed[index] = changed[index] + Fr::from(1);
        assert!(
            vk.verify(&params.verifier, &proof, changed.into_iter())
                .is_err(),
            "changed {label}"
        );
    }
    assert!(
        vk.verify(
            &params.verifier,
            &proof,
            root_statement[..5].iter().copied()
        )
        .is_err(),
        "depth 1 padding"
    );
    assert!(
        vk.verify(
            &params.verifier,
            &proof,
            root_statement.into_iter().chain([zero])
        )
        .is_err(),
        "depth 3 padding"
    );
    let mut missing_accumulator = proof;
    missing_accumulator.accumulators.clear();
    assert!(
        vk.verify(
            &params.verifier,
            &missing_accumulator,
            root_statement.into_iter()
        )
        .is_err(),
        "wrong accumulator count"
    );
}
