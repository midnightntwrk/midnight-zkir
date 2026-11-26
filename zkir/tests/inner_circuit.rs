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

//! Inner circuits: ZKIR circuits whose proofs another ZKIR circuit verifies
//! under a key it takes as a witness, bound to the key's `vk_id`.

#[path = "common/private_vk.rs"]
mod private_vk_common;
#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use midnight_zk_stdlib::Relation;
use midnight_zkir::ir_instructions::unbound_vk::INNER_ARCH;
use midnight_zkir::{InnerShape, IrSource, inner_circuit_vk_id};
use serialize::{tagged_deserialize, tagged_serialize};
use transient_crypto::curve::Fr;
use transient_crypto::hash::transient_hash;
use transient_crypto::proofs::{
    InnerProofWitness, InnerVkWitness, Proof, ProofPreimage, ProofTarget, ProverKey, VerifierKey,
    Zkir,
};

use crate::private_vk_common::{imm, input, load, private_verification_with};
use crate::verify_proof_common::{preimage_with, srs, test_rng};

/// The secret the guard proves knowledge of.
const SECRET: u64 = 0x5ec7e7;

/// The binding input of every guard proof, which the outer circuit fixes.
const GUARD_BINDING_INPUT: u64 = 0;

/// The guard: knowledge of a preimage of a public transient hash. Its
/// statement is `[binding_input, hash]`.
fn guard_ir(inner: Option<InnerShape>) -> IrSource {
    let mut ir = load(
        "",
        r#"{ "op": "private_input", "guard": null, "type": "Scalar<BLS12-381>", "output": "%x" },
           { "op": "transient_hash", "inputs": ["%x"], "output": "%h" },
           { "op": "impact", "guard": "0x01", "inputs": ["%h"] }"#,
    );
    ir.inner = inner;
    ir
}

/// The smallest size the guard fits in as an inner circuit.
fn guard_k() -> u8 {
    let ir = guard_ir(Some(InnerShape { k: 0 }));
    u8::try_from(midnight_zk_stdlib::optimal_k(&ir)).expect("k fits in u8")
}

fn inner_guard() -> IrSource {
    guard_ir(Some(InnerShape { k: guard_k() }))
}

fn guard_preimage(secret: u64) -> ProofPreimage {
    let mut preimage = preimage_with(vec![]);
    preimage.binding_input = Fr::from(GUARD_BINDING_INPUT);
    preimage.private_transcript = vec![Fr::from(secret)];
    preimage.public_transcript_inputs = vec![transient_hash(&[Fr::from(secret)])];
    preimage
}

fn guard_statement(secret: u64) -> Vec<Fr> {
    vec![
        Fr::from(GUARD_BINDING_INPUT),
        transient_hash(&[Fr::from(secret)]),
    ]
}

async fn keygen(ir: &IrSource) -> (ProverKey<IrSource>, VerifierKey) {
    ir.keygen(srs()).await.expect("keygen")
}

async fn prove(ir: &IrSource, pk: ProverKey<IrSource>, preimage: &ProofPreimage) -> Proof {
    let (proof, _, _) = ir
        .prove(test_rng(), srs(), pk, preimage)
        .await
        .expect("prove");
    proof
}

/// The outer circuit: verify a guard proof of the statement
/// `[GUARD_BINDING_INPUT, %s]` under the private key bound to the circuit input
/// `%h`, published so the verifier sees which key the proof was verified
/// under.
fn outer_ir(k: u8) -> IrSource {
    let binding = imm(Fr::from(GUARD_BINDING_INPUT));
    load(
        &[input("%h"), input("%s")].join(", "),
        &[
            r#"{ "op": "impact", "guard": "0x01", "inputs": ["%h"] }"#.to_string(),
            private_verification_with(
                0,
                ["0x01"; 3],
                k,
                2,
                r#""%h""#,
                &[binding.as_str(), r#""%s""#],
            ),
        ]
        .join(",\n"),
    )
}

/// The outer circuit's preimage, with the guard's key in the preimage itself.
fn outer_preimage(hash: Fr, statement: Fr, proof: &Proof, vk: &VerifierKey) -> ProofPreimage {
    let mut preimage = preimage_with(vec![InnerProofWitness::Direct(proof.bytes.clone())]);
    preimage.inputs = vec![hash, statement];
    preimage.public_transcript_inputs = vec![hash];
    preimage.inner_vks = vec![InnerVkWitness::from(vk)];
    preimage
}

#[test]
fn an_inner_shape_round_trips() {
    let ir = guard_ir(Some(InnerShape { k: 12 }));
    let json = serde_json::to_string(&ir).expect("serialize");
    assert!(json.contains(r#""inner":{"k":12}"#), "{json}");
    let mut bytes = Vec::new();
    tagged_serialize(&ir, &mut bytes).expect("tagged serialize");
    let back: IrSource = tagged_deserialize(&bytes[..]).expect("tagged deserialize");
    assert_eq!(back, ir);
}

#[test]
fn a_circuit_without_an_inner_shape_is_unchanged() {
    let ir = guard_ir(None);
    let json = serde_json::to_string(&ir).expect("serialize");
    assert!(!json.contains("inner\""), "{json}");
    assert_eq!(ir.target(), ProofTarget::Node);
    assert_ne!(ir.used_chips(), INNER_ARCH);
}

#[test]
fn an_inner_circuit_has_the_inner_shape() {
    let ir = guard_ir(Some(InnerShape { k: 17 }));
    assert_eq!(ir.k(), 17);
    assert_eq!(ir.target(), ProofTarget::Circuit);
    assert_eq!(ir.used_chips(), INNER_ARCH);
}

#[actix_rt::test]
async fn an_inner_circuit_must_fit_its_size() {
    let ir = guard_ir(Some(InnerShape { k: guard_k() - 1 }));
    let err = ir.keygen(srs()).await.err().expect("keygen must fail");
    assert!(err.to_string().contains("needs a size"), "{err}");
}

#[actix_rt::test]
async fn an_inner_circuit_cannot_verify_proofs() {
    let mut ir = outer_ir(guard_k());
    ir.inner = Some(InnerShape { k: 20 });
    let err = ir.keygen(srs()).await.err().expect("keygen must fail");
    assert!(err.to_string().contains("cannot verify proofs"), "{err}");
    let err = ir.check(&preimage_with(vec![])).expect_err("check must fail");
    assert!(err.to_string().contains("cannot verify proofs"), "{err}");
}

#[actix_rt::test]
async fn an_inner_proof_verifies_natively_for_a_circuit_only() {
    let ir = inner_guard();
    let (pk, vk) = keygen(&ir).await;
    let proof = prove(&ir, pk, &guard_preimage(SECRET)).await;
    assert!(proof.accumulators.is_empty());
    vk.verify_for(
        ProofTarget::Circuit,
        &srs().verifier,
        &proof,
        guard_statement(SECRET).into_iter(),
    )
    .expect("the proof verifies over the circuit transcript");
    assert!(
        vk.verify_for(
            ProofTarget::Circuit,
            &srs().verifier,
            &proof,
            guard_statement(SECRET + 1).into_iter()
        )
        .is_err(),
        "the proof does not verify against another statement"
    );
    assert!(
        vk.verify(&srs().verifier, &proof, guard_statement(SECRET).into_iter())
            .is_err(),
        "the proof does not verify over the node transcript"
    );
}

#[actix_rt::test]
async fn the_outer_circuit_checks_a_key_from_the_preimage() {
    let guard = inner_guard();
    let (pk, vk) = keygen(&guard).await;
    let proof = prove(&guard, pk, &guard_preimage(SECRET)).await;
    let id = inner_circuit_vk_id(&vk).expect("vk_id");
    let statement = transient_hash(&[Fr::from(SECRET)]);
    let outer = outer_ir(guard_k());

    outer
        .check(&outer_preimage(id, statement, &proof, &vk))
        .expect("the outer circuit accepts the guard's key bound to its vk_id");

    let err = outer
        .check(&outer_preimage(id + Fr::from(1u64), statement, &proof, &vk))
        .expect_err("another vk_id must be rejected");
    assert!(format!("{err:#}").to_lowercase().contains("vk"), "{err:#}");

    let mut missing = outer_preimage(id, statement, &proof, &vk);
    missing.inner_vks = vec![];
    assert!(
        outer.check(&missing).is_err(),
        "a preimage without the key must be rejected"
    );
}

#[actix_rt::test]
async fn the_outer_circuit_rejects_the_key_of_a_node_circuit() {
    let node_guard = guard_ir(None);
    let (_, node_vk) = keygen(&node_guard).await;
    assert!(
        inner_circuit_vk_id(&node_vk).is_ok(),
        "a node circuit's key still has a vk_id"
    );
    let inner = inner_guard();
    let (pk, _) = keygen(&inner).await;
    let proof = prove(&inner, pk, &guard_preimage(SECRET)).await;
    let statement = transient_hash(&[Fr::from(SECRET)]);
    let id = inner_circuit_vk_id(&node_vk).expect("vk_id");
    let err = outer_ir(guard_k())
        .check(&outer_preimage(id, statement, &proof, &node_vk))
        .expect_err("a key not of the inner shape must be rejected");
    assert!(
        format!("{err:#}").contains("every chip enabled")
            || format!("{err:#}").contains("expected a key of size"),
        "{err:#}"
    );
}

/// The whole path through the [`Zkir`] trait: the outer proof verifies the
/// guard proof in-circuit, under the key the preimage carries.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn the_outer_proof_verifies_an_inner_circuit_proof() {
    let guard = inner_guard();
    let (pk, vk) = keygen(&guard).await;
    let proof = prove(&guard, pk, &guard_preimage(SECRET)).await;
    let id = inner_circuit_vk_id(&vk).expect("vk_id");
    let statement = transient_hash(&[Fr::from(SECRET)]);

    let outer = outer_ir(guard_k());
    println!("guard k = {}, outer k = {}", guard_k(), outer.k());
    let (outer_pk, outer_vk) = keygen(&outer).await;
    let preimage = outer_preimage(id, statement, &proof, &vk);
    let (outer_proof, pis, _) = outer
        .prove(test_rng(), srs(), outer_pk, &preimage)
        .await
        .expect("outer prove");
    assert_eq!(outer_proof.accumulators.len(), 1);
    outer_vk
        .verify(&srs().verifier, &outer_proof, pis.into_iter())
        .expect("outer verify, including the deferred pairing");
}
