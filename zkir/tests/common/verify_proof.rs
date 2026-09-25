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

//! Helpers shared by `verify_proof.rs` and `verify_proof_e2e.rs`.
//!
//! Included with `#[path]` rather than via `common/mod.rs`, which needs
//! `MIDNIGHT_PP` at compile time.
#![allow(dead_code)]

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::{Arc, Mutex, OnceLock};
use std::time::Instant;

use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_circuits::instructions::{AssignmentInstructions, PublicInputInstructions};
use midnight_circuits::types::AssignedNative;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::circuit::{Layouter, Value};
use midnight_proofs::plonk;
use midnight_proofs::poly::kzg::params::ParamsKZG;
use midnight_proofs::utils::SerdeFormat;
use midnight_zk_stdlib::{
    MidnightPK, Relation, ZkStdLib, ZkStdLibArch, optimal_k, prove, setup_pk, setup_vk,
};
use midnight_zkir::IrSource;
use midnight_zkir::decider::{DeciderKind, serialize_vk};
use midnight_zkir::ir::IrMinorVersion;
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use sha2::Digest;
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{
    InnerProofWitness, KeyLocation, ParamsProver, ParamsProverProvider, ParamsVerifier,
    ProofPreimage,
};

/// The binding input every preimage carries, as public input 0.
pub const BINDING_INPUT: u64 = 99;

/// A VK blob's SHA-256, as hex without `0x`: the `vk_hash` `verify_proof` stores.
pub fn vk_hash_hex(vk_blob: &[u8]) -> String {
    const_hex::encode(sha2::Sha256::digest(vk_blob))
}

/// Parses an IR from its JSON parts, as [`IrMinorVersion::V0`].
pub fn load_ir(inputs: &str, do_communications_commitment: bool, instructions: &str) -> IrSource {
    let json = format!(
        r#"{{
           "version": {{ "major": 3, "minor": 0 }},
           "inputs": [{inputs}],
           "outputs": [],
           "do_communications_commitment": {do_communications_commitment},
           "instructions": [{instructions}]
        }}"#
    );
    IrSource::load(json.as_bytes()).expect("IR must parse")
}

/// Attaches a VK side-table, bumping to [`IrMinorVersion::V1`] since a `V0`
/// cannot carry one.
pub fn with_vks(mut ir: IrSource, vks: Vec<Vec<u8>>) -> IrSource {
    ir.version = IrMinorVersion::V1;
    ir.verify_proof_vks = vks;
    ir
}

/// A preimage carrying only [`BINDING_INPUT`] and `inner_proofs`.
pub fn preimage_with(inner_proofs: Vec<InnerProofWitness>) -> ProofPreimage {
    ProofPreimage {
        binding_input: Fr::from(BINDING_INPUT),
        communications_commitment: None,
        inputs: vec![],
        private_transcript: vec![],
        public_transcript_inputs: vec![],
        public_transcript_outputs: vec![],
        inner_proofs,
        key_location: KeyLocation(Cow::Borrowed("builtin")),
    }
}

/// Seed for the generated SRS.
pub const SRS_SEED: [u8; 32] = [42; 32];

/// Cache for [`srs`].
static SRS: OnceLock<GeneratedParams> = OnceLock::new();

/// An SRS generated in-process, rather than read from `$MIDNIGHT_PP`.
///
/// The published parameters stop at degree 17, and in-circuit proof
/// verification needs more, so these tests would otherwise require two
/// downloads totalling 150MB that no other test wants. Nothing here proves
/// anything about soundness, so a known toxic waste costs us nothing.
pub struct GeneratedParams {
    /// Verifier parameters for this SRS. The global `PARAMS_VERIFIER` belongs to
    /// a different setup, so proofs made here do not verify against it.
    pub verifier: ParamsVerifier,
    /// Generated per `k` from [`SRS_SEED`]. `unsafe_setup` draws the secret
    /// first, so every degree shares one setup, as verifying an inner proof
    /// against an outer one requires.
    by_k: Mutex<HashMap<u8, ParamsProver>>,
}

impl GeneratedParams {
    pub fn params_for(&self, k: u8) -> ParamsProver {
        let mut cache = self.by_k.lock().expect("params cache");
        cache
            .entry(k)
            .or_insert_with(|| {
                let params = ParamsKZG::<Bls12>::unsafe_setup(k as u32, srs_rng());
                ParamsProver(Arc::new(params))
            })
            .clone()
    }
}

impl ParamsProverProvider for GeneratedParams {
    async fn get_params(&self, k: u8) -> std::io::Result<ParamsProver> {
        Ok(self.params_for(k))
    }
}

/// The shared [`GeneratedParams`].
pub fn srs() -> &'static GeneratedParams {
    SRS.get_or_init(|| {
        // `ParamsVerifier` is only constructible by reading an SRS, so the
        // generated one takes a round-trip through that. Verifier parameters
        // hold nothing but `G2` elements, so a one-degree SRS carrying the same
        // `s_g2` yields the same result as the full one, for a few hundred bytes
        // rather than a hundred megabytes.
        let mut bytes = Vec::new();
        ParamsKZG::<Bls12>::unsafe_setup(1, srs_rng())
            .write_custom(&mut bytes, SerdeFormat::RawBytesUnchecked)
            .expect("write generated params");
        GeneratedParams {
            verifier: ParamsVerifier::read(&bytes[..]).expect("read generated verifier params"),
            by_k: Mutex::new(HashMap::new()),
        }
    })
}

pub fn srs_rng() -> ChaCha20Rng {
    ChaCha20Rng::from_seed(SRS_SEED)
}

/// Exposes one field element as its only public input.
#[derive(Clone, Default)]
pub struct SingleScalarRelation;

impl Relation for SingleScalarRelation {
    type Instance = Fq;
    type Witness = ();
    type Error = plonk::Error;

    fn format_instance(instance: &Fq) -> Result<Vec<Fq>, plonk::Error> {
        Ok(vec![*instance])
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        instance: Value<Fq>,
        _witness: Value<()>,
    ) -> Result<(), plonk::Error> {
        let x: AssignedNative<Fq> = std_lib.assign(layouter, instance)?;
        std_lib.constrain_as_public_input(layouter, &x)?;
        Ok(())
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch::default()
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(SingleScalarRelation)
    }
}

/// Keygen for `R` at its own `k`, returning the VK as a `None`-decider blob.
pub async fn inner_setup_for<R: Relation + Default>(
    label: &str,
) -> (ParamsProver, MidnightPK<R>, Vec<u8>) {
    let k = u8::try_from(optimal_k(&R::default())).expect("inner k fits in u8");
    inner_setup_at::<R>(label, k).await
}

/// As [`inner_setup_for`], at a chosen `k`.
pub async fn inner_setup_at<R: Relation + Default>(
    label: &str,
    k: u8,
) -> (ParamsProver, MidnightPK<R>, Vec<u8>) {
    let relation = R::default();
    println!("inner circuit k = {k} ({label})");

    // The VK takes its `k` from the SRS.
    let inner_srs = srs().params_for(k);
    let inner_vk = setup_vk(inner_srs.as_ref(), &relation);
    assert_eq!(
        inner_vk.k(),
        k,
        "inner SRS must match the k it was set up with"
    );
    let inner_pk = setup_pk(&relation, &inner_vk);

    let vk_blob = serialize_vk(&inner_vk, DeciderKind::None).expect("serialize inner vk");

    (inner_srs, inner_pk, vk_blob)
}

/// Proves with the Poseidon transcript, which the in-circuit verifier requires.
pub fn prove_inner_for<R: Relation + Default>(
    label: &str,
    instance: &R::Instance,
    witness: R::Witness,
    inner_pk: &MidnightPK<R>,
    inner_srs: &ParamsProver,
    rng: &mut ChaCha20Rng,
) -> Vec<u8> {
    let t = Instant::now();
    let proof = prove::<R, PoseidonState<Fq>>(
        inner_srs.as_ref(),
        inner_pk,
        &R::default(),
        instance,
        witness,
        rng,
    )
    .expect("inner prove");
    println!(
        "inner prove ({label}): {:.1?} ({} proof bytes)",
        t.elapsed(),
        proof.len()
    );
    proof
}

/// An inner proof with its VK blob and public inputs.
pub struct InnerProof {
    pub vk_blob: Vec<u8>,
    pub pis: Vec<Fq>,
    pub proof: Vec<u8>,
}

impl InnerProof {
    /// As an `outer_ir_for_all` entry.
    pub fn entry(&self) -> (Vec<u8>, Vec<Fq>) {
        (self.vk_blob.clone(), self.pis.clone())
    }
}

/// A [`SingleScalarRelation`] proof of `123`.
pub async fn scalar_inner_proof(rng: &mut ChaCha20Rng) -> InnerProof {
    scalar_inner_proofs(&[123], rng).await.pop().expect("one")
}

/// [`SingleScalarRelation`] proofs of each instance, under one key.
pub async fn scalar_inner_proofs(instances: &[u64], rng: &mut ChaCha20Rng) -> Vec<InnerProof> {
    let (srs, pk, vk_blob) = inner_setup_for::<SingleScalarRelation>("single-scalar").await;
    instances
        .iter()
        .map(|&i| {
            let instance = Fq::from(i);
            let proof = prove_inner_for::<SingleScalarRelation>(
                &format!("single-scalar, instance {i}"),
                &instance,
                (),
                &pk,
                &srs,
                rng,
            );
            InnerProof {
                vk_blob: vk_blob.clone(),
                pis: SingleScalarRelation::format_instance(&instance)
                    .expect("format scalar instance"),
                proof,
            }
        })
        .collect()
}

/// A fixed-seed RNG, so tests are reproducible.
pub fn test_rng() -> ChaCha20Rng {
    ChaCha20Rng::from_seed([7; 32])
}
