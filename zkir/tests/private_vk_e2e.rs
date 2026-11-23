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

//! End-to-end tests for verifying inner proofs under private verifying keys:
//! each builds an outer circuit, proves it with `prove_with_inner_vks`, and
//! verifies the outer proof, including the deferred pairing.
//!
//! The outer circuits need more than the published parameters provide, so
//! these use the SRS generated in-process, and are `#[ignore]`d for runtime.

#[path = "common/private_vk.rs"]
mod private_vk_common;
#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use std::collections::HashMap;
use std::sync::Arc;

use midnight_curves::Fq;
use midnight_proofs::plonk::VerifyingKey;
use midnight_zk_stdlib::KZG;
use midnight_zkir::ir_types::{InnerVk, IrValue};
use midnight_zkir::{Identifier, IrSource, Preprocessed};
use rand_chacha::ChaCha20Rng;
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{Proof, ProofPreimage, ProverKey, VerifierKey, Zkir};

use crate::private_vk_common::{
    PREIMAGE, guarded_off_preimage, honest_preimage, input, key_a, key_b, load,
    one_private_preimage, one_private_verification,
};
use crate::verify_proof_common::{BINDING_INPUT, srs, test_rng};

/// An inner proof verifies under a private key, and the outer statement
/// publishes the key's `vk_id`.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn inner_proof_verifies_under_a_private_key() {
    let mut rng = test_rng();
    let key = key_a();
    let (ir, pk, vk) = outer_setup(key.k()).await;

    let preimage = honest_preimage(key, &mut rng);
    let (proof, pis) = outer_prove(&ir, pk, &preimage, &[Some(key.plonk_vk())], &mut rng)
        .await
        .expect("outer prove");
    assert!(
        pis.contains(&key.id()),
        "the statement publishes the key's vk_id"
    );
    outer_verify(&vk, &proof, pis).expect("outer verify");
}

/// One outer circuit verifies proofs under any key of the right shape and size:
/// the key is chosen at proving time.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn one_outer_circuit_verifies_proofs_under_different_keys() {
    let mut rng = test_rng();
    let (ir, pk, vk) = outer_setup(key_a().k()).await;

    for key in [key_a(), key_b()] {
        let preimage = honest_preimage(key, &mut rng);
        let (proof, pis) = outer_prove(
            &ir,
            pk.clone(),
            &preimage,
            &[Some(key.plonk_vk())],
            &mut rng,
        )
        .await
        .expect("outer prove");
        outer_verify(&vk, &proof, pis).expect("outer verify");
    }
}

/// A proof made under another key than the bound one is rejected, at proving
/// or at verification.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn proof_under_another_key_is_rejected() {
    let mut rng = test_rng();
    let (a, b) = (key_a(), key_b());
    let (ir, pk, vk) = outer_setup(a.k()).await;

    // A valid proof of a valid statement, only under the wrong key.
    let preimage = one_private_preimage(
        a.id(),
        true,
        b.statement(PREIMAGE),
        b.prove(PREIMAGE, &mut rng),
    );
    let outcome = outer_prove(&ir, pk, &preimage, &[Some(a.plonk_vk())], &mut rng)
        .await
        .and_then(|(proof, pis)| outer_verify(&vk, &proof, pis));
    assert!(
        outcome.is_err(),
        "a proof under another key must not verify"
    );
}

/// Guarded off, the circuit proves with no key, no inner proof and no hash,
/// and the same keys serve both guard values.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn guarded_off_needs_no_key_or_proof() {
    let mut rng = test_rng();
    let key = key_a();
    let (ir, pk, vk) = outer_setup(key.k()).await;

    let off = guarded_off_preimage();
    let (proof, pis) = outer_prove(&ir, pk.clone(), &off, &[None], &mut rng)
        .await
        .expect("outer prove, guarded off");
    outer_verify(&vk, &proof, pis).expect("outer verify, guarded off");

    let on = honest_preimage(key, &mut rng);
    let (proof, pis) = outer_prove(&ir, pk, &on, &[Some(key.plonk_vk())], &mut rng)
        .await
        .expect("outer prove, guarded on");
    outer_verify(&vk, &proof, pis).expect("outer verify, guarded on");
}

/// A malicious prover that skips the off-circuit checks cannot witness a key
/// other than the one the hash names: `bind_vk` is enforced in-circuit. The
/// honest key is the control.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn bind_vk_is_enforced_in_circuit() {
    let (a, b) = (key_a(), key_b());
    let ir = load(
        &input("%h"),
        &format!(
            r#"{{ "op": "assign_unbound_vk", "guard": "0x01", "k": {k}, "nb_public_inputs": 1,
                  "output": "%u" }},
               {{ "op": "bind_vk", "guard": "0x01", "vk": "%u", "hash": "%h", "output": "%b" }}"#,
            k = a.k(),
        ),
    );
    let (pk, vk) = outer_keygen(&ir).await;

    for (witnessed, is_valid) in [(a, true), (b, false)] {
        let preproc = Preprocessed {
            memory: HashMap::from([
                (Identifier("%h".into()), IrValue::Native(a.id())),
                (
                    Identifier("%u".into()),
                    IrValue::UnboundVk(InnerVk(Arc::new(witnessed.plonk_vk()))),
                ),
            ]),
            pis: vec![BINDING_INPUT.into()],
            pi_skips: vec![],
            binding_input: BINDING_INPUT.into(),
            comm_comm: None,
            inner_proofs: vec![],
        };
        let verified = ir
            .prove_unchecked(&mut test_rng(), srs(), pk.clone(), preproc)
            .await
            .and_then(|proof| {
                vk.verify(
                    &srs().verifier,
                    &proof,
                    [Fr::from(BINDING_INPUT)].into_iter(),
                )
            });
        assert_eq!(verified.is_ok(), is_valid);
    }
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Builds [`one_private_verification`] for keys of size `2^k` and runs keygen.
/// Keygen needs no key: the circuit depends only on the shape and size.
async fn outer_setup(k: u8) -> (IrSource, ProverKey<IrSource>, VerifierKey) {
    let ir = one_private_verification(k);
    let (pk, vk) = outer_keygen(&ir).await;
    (ir, pk, vk)
}

async fn outer_keygen(ir: &IrSource) -> (ProverKey<IrSource>, VerifierKey) {
    println!("outer circuit k = {}", ir.k());
    ir.keygen(srs()).await.expect("outer keygen")
}

/// Proves the outer circuit with `keys` handed over out of band.
async fn outer_prove(
    ir: &IrSource,
    pk: ProverKey<IrSource>,
    preimage: &ProofPreimage,
    keys: &[Option<VerifyingKey<Fq, KZG>>],
    rng: &mut ChaCha20Rng,
) -> anyhow::Result<(Proof, Vec<Fr>)> {
    let (proof, pis, _skips) = ir
        .prove_with_inner_vks(rng, srs(), pk, preimage, keys)
        .await?;
    Ok((proof, pis))
}

/// Verifies the outer proof, including the pairing on every accumulator.
fn outer_verify(vk: &VerifierKey, proof: &Proof, pis: Vec<Fr>) -> anyhow::Result<()> {
    vk.verify(&srs().verifier, proof, pis.into_iter())
}
