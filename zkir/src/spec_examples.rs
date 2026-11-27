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

//! These tests read the JSON examples directly from the v4 language reference
//! so that changes to the examples are checked against the Rust VM.  They live
//! under `src/` because they call the crate-private `IrSource::preprocess` to
//! check the public inputs and skip list.  The recursive examples substitute
//! the generated scalar circuit's fixed key for the placeholder in the text.

#[path = "../tests/common/verify_proof.rs"]
mod fixture;

use crate::ir::{Identifier, Instruction, IrSource};
use crate::ir_instructions::accumulate::{accumulate_offcircuit, trivial_accumulator};
use crate::ir_instructions::prepare_verification::prepare_verification_offcircuit;
use crate::ir_types::IrValue;
use fixture::{BINDING_INPUT, preimage_with, scalar_inner_proof, srs, test_rng};
use sha2::{Digest, Sha256};
use std::sync::Arc;
use transient_crypto::curve::Fr;
use transient_crypto::hash::transient_hash;
use transient_crypto::proofs::{InnerProofWitness, Zkir};

fn example(section: &str) -> IrSource {
    let spec = std::fs::read_to_string("../zkir-spec/docs/zkir-v4-spec.md")
        .expect("read the language specification");
    let (_, body) = spec.split_once(section).expect("worked example heading");
    let (_, fence) = body.split_once("```json\n").expect("JSON example");
    let (json, _) = fence.split_once("\n```").expect("closing JSON fence");
    IrSource::load(json.as_bytes()).expect("example loads as IR 4.0")
}

#[test]
fn byte_packing() {
    let ir = example("### 7.1 Byte packing");
    let mut preimage = preimage_with(vec![]);
    preimage.public_transcript_inputs = vec![0.into(), 42.into()];
    let run = ir.preprocess(&preimage).expect("byte example accepts");
    let expected = vec![Fr::from(BINDING_INPUT).0, Fr::from(0).0, Fr::from(42).0];
    assert_eq!(run.pis, expected);
    assert_eq!(run.pi_skips, vec![None]);
    let mut bytes = vec![0u8; 32];
    bytes[31] = 42;
    assert_eq!(
        run.memory[&Identifier("%roundtrip".into())],
        IrValue::Bytes(bytes)
    );
}

#[actix_rt::test]
async fn hash_preimage_and_nullifier() {
    let ir = example("### 7.4 A hash preimage");
    let x = Fr::from(7);
    let r = Fr::from(11);
    let digest = transient_hash(&[x, r]);
    let nullifier = transient_hash(&[x]);
    let mut preimage = preimage_with(vec![]);
    preimage.private_transcript = vec![x, r];
    preimage.public_transcript_outputs = vec![digest];
    preimage.public_transcript_inputs = vec![nullifier];

    let params = srs();
    let (pk, vk) = ir
        .keygen(params)
        .await
        .expect("generate nullifier example keys");
    let (proof, statement, skips) = ir
        .prove(&mut test_rng(), params, pk, &preimage)
        .await
        .expect("prove nullifier example");
    assert_eq!(statement, vec![Fr::from(BINDING_INPUT), nullifier]);
    assert_eq!(skips, vec![None]);
    assert!(proof.accumulators.is_empty());
    vk.verify(&params.verifier, &proof, statement.into_iter())
        .expect("verify binding input and nullifier");
}

#[actix_rt::test]
async fn fixed_key_and_folded_statements() {
    recursive_examples(false).await;
}

#[actix_rt::test]
#[ignore = "generates two outer key pairs and proves all four reference instances"]
async fn verify_reference_proofs() {
    recursive_examples(true).await;
}

async fn recursive_examples(verify_outer: bool) {
    let mut rng = test_rng();
    let inner = scalar_inner_proof(&mut rng).await;
    let active = prepare_verification_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
        .expect("prepare scalar proof");
    for (section, folded) in [("### 7.2 Fixed key", false), ("### 7.3 Fold", true)] {
        let mut ir = example(section);
        assert_eq!(ir.inner_vks, vec![vec![0]]);
        let template_digest = Sha256::digest(&ir.inner_vks[0]).to_vec();
        ir.inner_vks = vec![inner.vk_blob.clone()];
        for instruction in Arc::make_mut(&mut ir.instructions) {
            if let Instruction::PrepareVerification { vk_hash, .. } = instruction {
                assert_eq!(*vk_hash, template_digest);
                *vk_hash = Sha256::digest(&inner.vk_blob).to_vec();
            }
        }
        let keys = if verify_outer {
            Some(
                ir.keygen(srs())
                    .await
                    .expect("generate reference example keys"),
            )
        } else {
            None
        };
        for guard in [false, true] {
            let last = if guard { inner.proof.clone() } else { vec![42] };
            let mut slots = vec![];
            if folded {
                slots.push(InnerProofWitness::Direct(inner.proof.clone()));
            }
            slots.push(InnerProofWitness::Direct(last));
            let mut preimage = preimage_with(slots);
            preimage.inputs = vec![Fr::from(u64::from(guard))];
            let mut statement = vec![BINDING_INPUT];
            let mut skips = vec![];
            if folded {
                preimage.public_transcript_inputs = vec![42.into()];
                if guard {
                    preimage
                        .public_transcript_inputs
                        .extend([Fr::from(7), Fr::from(8)]);
                }
                statement.extend(if guard { [42, 7, 8] } else { [42, 0, 0] });
                skips.extend([None, if guard { None } else { Some(2) }]);
            }
            let run = ir.preprocess(&preimage).expect("fixed-key source accepts");
            let conditional = if guard { active } else { trivial_accumulator() };
            let expected = if folded {
                accumulate_offcircuit(&[active, conditional]).unwrap()
            } else {
                conditional
            };
            let mut pis = expected.as_public_input();
            pis.extend(statement.iter().map(|&x| Fr::from(x).0));
            assert_eq!(ir.accumulator_count(), 1);
            assert_eq!(run.pis, pis);
            assert_eq!(run.pi_skips, skips);
            assert_eq!(run.inner_proofs.last().unwrap().is_empty(), !guard);
            if let Some((pk, vk)) = &keys {
                let (proof, returned, proof_skips) = ir
                    .prove(&mut rng, srs(), pk.clone(), &preimage)
                    .await
                    .expect("prove reference example");
                assert_eq!(
                    returned,
                    statement.into_iter().map(Fr::from).collect::<Vec<_>>()
                );
                assert_eq!(proof_skips, skips);
                assert_eq!(proof.accumulators.len(), 1);
                assert_eq!(
                    proof.accumulators[0].as_public_input(),
                    expected.as_public_input()
                );
                vk.verify(&srs().verifier, &proof, returned.into_iter())
                    .expect("verify reference statement and deferred pairing");
            }
        }
    }
}
