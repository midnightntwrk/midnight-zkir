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

//! Fixtures for verifying inner proofs under private verifying keys: a key is
//! witnessed with `assign_unbound_vk`, bound to its `vk_id` with `bind_vk`, and
//! the resulting `BoundVk` is passed to `prepare_verification`.
//!
//! Keys reach zkir out of band, one per `assign_unbound_vk` in instruction
//! order, through `IrSource::check_with_inner_vks` and
//! `IrSource::prove_with_inner_vks`.

#![allow(dead_code)]

use std::sync::OnceLock;

use midnight_circuits::hash::poseidon::{PoseidonChip, PoseidonState};
use midnight_circuits::instructions::hash::HashCPU;
use midnight_circuits::instructions::{AssignmentInstructions, PublicInputInstructions};
use midnight_circuits::types::AssignedNative;
use midnight_curves::Fq;
use midnight_proofs::circuit::{Layouter, Value};
use midnight_proofs::plonk::{self, VerifyingKey};
use midnight_proofs::utils::SerdeFormat;
use midnight_zk_stdlib::{
    KZG, MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch, optimal_k, prove, setup_pk,
    setup_vk,
};
use midnight_zkir::ir::Operand;
use midnight_zkir::ir_instructions::unbound_vk::INNER_ARCH;
use midnight_zkir::{IrSource, vk_id};
use rand_chacha::ChaCha20Rng;
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{InnerProofWitness, ProofPreimage};

use crate::verify_proof_common::{preimage_with, srs};

/// The public inputs of a [`PrivateInner`] proof: the hash.
pub const NB_PUBLIC_INPUTS: usize = 1;

/// The preimage [`PrivateKey::prove`] proves knowledge of in most tests.
pub const PREIMAGE: u64 = 123;

/// An inner circuit of the one shape private keys may have ([`INNER_ARCH`]):
/// the prover knows a preimage `x` of the public hash `h = Poseidon(tag, x)`.
/// `tag` is a circuit constant, so it changes the key without changing its
/// shape.
#[derive(Clone)]
pub struct PrivateInner {
    pub tag: u64,
}

impl PrivateInner {
    /// The hash a proof of knowledge of `preimage` exposes.
    pub fn hash(&self, preimage: Fq) -> Fq {
        <PoseidonChip<Fq> as HashCPU<Fq, Fq>>::hash(&[Fq::from(self.tag), preimage])
    }
}

impl Relation for PrivateInner {
    type Instance = Fq;
    type Witness = Fq;
    type Error = plonk::Error;

    fn format_instance(hash: &Fq) -> Result<Vec<Fq>, plonk::Error> {
        Ok(vec![*hash])
    }

    fn circuit(
        &self,
        std: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        _hash: Value<Fq>,
        preimage: Value<Fq>,
    ) -> Result<(), plonk::Error> {
        let tag: AssignedNative<Fq> = std.assign_fixed(layouter, Fq::from(self.tag))?;
        let x: AssignedNative<Fq> = std.assign(layouter, preimage)?;
        let h = std.poseidon(layouter, &[tag, x])?;
        std.constrain_as_public_input(layouter, &h)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        INNER_ARCH
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&self.tag.to_le_bytes())
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut bytes = [0u8; 8];
        reader.read_exact(&mut bytes)?;
        Ok(PrivateInner {
            tag: u64::from_le_bytes(bytes),
        })
    }
}

/// A [`PrivateInner`] key pair, set up against the shared generated SRS so its
/// proofs verify inside an outer circuit.
pub struct PrivateKey {
    pub relation: PrivateInner,
    pub vk: MidnightVK<KZG>,
    pub pk: MidnightPK<PrivateInner, KZG>,
}

impl PrivateKey {
    /// Sets up the key of `PrivateInner { tag }` at size `2^k`.
    pub fn at(tag: u64, k: u8) -> Self {
        let relation = PrivateInner { tag };
        let vk = setup_vk::<_, KZG>(srs().params_for(k).as_ref(), &relation);
        assert_eq!(vk.k(), k, "the key takes its size from the SRS");
        let pk = setup_pk(&relation, &vk);
        PrivateKey { relation, vk, pk }
    }

    /// Sets up the key of `PrivateInner { tag }` at its smallest size.
    pub fn new(tag: u64) -> Self {
        Self::at(tag, inner_k())
    }

    pub fn k(&self) -> u8 {
        self.vk.k()
    }

    /// The key as the provider hands it to zkir.
    pub fn plonk_vk(&self) -> VerifyingKey<Fq, KZG> {
        self.vk.vk().clone()
    }

    /// The key's identity: what `bind_vk` checks it against, and what names it
    /// in a fixed-key `prepare_verification`.
    pub fn id(&self) -> Fr {
        vk_id(self.vk.vk(), NB_PUBLIC_INPUTS)
    }

    /// The key serialized for the fixed-key side-table, `IrSource::inner_vks`.
    pub fn blob(&self) -> Vec<u8> {
        let mut blob = Vec::new();
        self.vk
            .write(&mut blob, SerdeFormat::Processed)
            .expect("serialize inner vk");
        blob
    }

    /// The statement of a proof of knowledge of `preimage` under this key: its
    /// hash.
    pub fn statement(&self, preimage: u64) -> Fr {
        Fr(self.relation.hash(Fq::from(preimage)))
    }

    /// A proof of knowledge of `preimage` under this key, with the Poseidon
    /// transcript the in-circuit verifier requires.
    pub fn prove(&self, preimage: u64, rng: &mut ChaCha20Rng) -> Vec<u8> {
        let preimage = Fq::from(preimage);
        prove::<PrivateInner, PoseidonState<Fq>, KZG>(
            srs().params_for(self.k()).as_ref(),
            &self.pk,
            &self.relation,
            &self.relation.hash(preimage),
            preimage,
            rng,
        )
        .expect("inner prove")
    }
}

/// The smallest size a [`PrivateInner`] circuit fits in.
pub fn inner_k() -> u8 {
    static K: OnceLock<u8> = OnceLock::new();
    *K.get_or_init(|| {
        u8::try_from(optimal_k(&PrivateInner { tag: 0 })).expect("inner k fits in u8")
    })
}

/// A key of the right shape whose `vk_id` is [`key_a`]'s hash in most tests.
pub fn key_a() -> &'static PrivateKey {
    static KEY: OnceLock<PrivateKey> = OnceLock::new();
    KEY.get_or_init(|| PrivateKey::new(1))
}

/// Another key of the same shape and size as [`key_a`].
pub fn key_b() -> &'static PrivateKey {
    static KEY: OnceLock<PrivateKey> = OnceLock::new();
    KEY.get_or_init(|| PrivateKey::new(2))
}

/// `x` as an IR operand: the canonical `0x`-hex immediate, quoted.
pub fn imm(x: Fr) -> String {
    serde_json::to_string(&Operand::Immediate(x)).expect("operand serializes")
}

/// A `load_constant` of the fixed key named by its `vk_id`, into the `BoundVk`
/// variable `output`.
pub fn fixed_vk(output: &str, id: Fr) -> String {
    format!(
        r#"{{ "op": "load_constant", "type": "BoundVk", "encoding": [{}], "output": "{output}" }}"#,
        imm(id)
    )
}

/// A `prepare_verification` `vk` field passing a `BoundVk` variable.
pub fn bound_vk(var: &str) -> String {
    format!(r#""{var}""#)
}

/// Parses an IR from its inputs and instructions, without a fixed-key side-table.
pub fn try_load(inputs: &str, instructions: &str) -> std::io::Result<IrSource> {
    let json = format!(
        r#"{{
           "version": {{ "major": 4, "minor": 0 }},
           "inputs": [{inputs}],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": [{instructions}]
        }}"#
    );
    IrSource::load(json.as_bytes())
}

/// As [`try_load`], panicking if the IR does not parse.
pub fn load(inputs: &str, instructions: &str) -> IrSource {
    try_load(inputs, instructions).expect("IR must parse")
}

/// A circuit input of type `Native`.
pub fn input(name: &str) -> String {
    format!(r#"{{ "name": "{name}", "type": "Scalar<BLS12-381>" }}"#)
}

/// Verifies inner proof `%p_{i}` of `statement` under the private key in slot
/// `i`, bound to `hash`, all under `guard`.
pub fn private_verification(i: usize, guard: &str, k: u8, hash: &str, statement: &str) -> String {
    private_verification_with(i, [guard; 3], k, NB_PUBLIC_INPUTS, hash, &[statement])
}

/// [`private_verification`] with every knob exposed: the guards of
/// `assign_unbound_vk`, `bind_vk` and `prepare_verification` (in that order;
/// `inner_proof` takes the last), the key's declared public inputs, and the
/// instance.
pub fn private_verification_with(
    i: usize,
    [assign_guard, bind_guard, prepare_guard]: [&str; 3],
    k: u8,
    nb_public_inputs: usize,
    hash: &str,
    instance: &[&str],
) -> String {
    let instance = instance.join(", ");
    format!(
        r#"{{ "op": "inner_proof", "guard": "{prepare_guard}", "output": "%p_{i}" }},
           {{ "op": "assign_unbound_vk", "guard": "{assign_guard}", "k": {k},
              "nb_public_inputs": {nb_public_inputs}, "output": "%u_{i}" }},
           {{ "op": "bind_vk", "guard": "{bind_guard}", "vk": "%u_{i}", "hash": {hash},
              "output": "%b_{i}" }},
           {{ "op": "prepare_verification", "guard": "{prepare_guard}", "vk": {vk},
              "instance": [{instance}], "proof": "%p_{i}", "output": "%a_{i}" }},
           {{ "op": "verify_accumulator", "input": "%a_{i}" }}"#,
        vk = bound_vk(&format!("%b_{i}")),
    )
}

/// The canonical one-proof circuit: verify a proof of the inner statement `%s`
/// under the private key in slot 0, bound to the circuit input `%h`, under the
/// circuit input guard `%g`. The hash is published with `impact`, so the
/// verifier sees which key the proof was verified under: this is what makes
/// the hash trusted.
pub fn one_private_verification(k: u8) -> IrSource {
    load(
        &[input("%h"), input("%g"), input("%s")].join(", "),
        &[
            r#"{ "op": "impact", "guard": "%g", "inputs": ["%h"] }"#.to_string(),
            private_verification(0, "%g", k, r#""%h""#, r#""%s""#),
        ]
        .join(",\n"),
    )
}

/// The preimage of [`one_private_verification`]: the hash, guard and inner
/// statement as circuit inputs, the hash again as the published value when
/// guarded on, and the inner proof, which is blank when guarded off.
pub fn one_private_preimage(hash: Fr, guard: bool, statement: Fr, proof: Vec<u8>) -> ProofPreimage {
    let mut preimage = preimage_with(vec![InnerProofWitness::Direct(proof)]);
    preimage.inputs = vec![hash, Fr::from(guard as u64), statement];
    if guard {
        preimage.public_transcript_inputs = vec![hash];
    }
    preimage
}

/// [`one_private_preimage`] for a proof of knowledge of [`PREIMAGE`] under
/// `key`, bound to `key`'s own `vk_id`.
pub fn honest_preimage(key: &PrivateKey, rng: &mut ChaCha20Rng) -> ProofPreimage {
    one_private_preimage(
        key.id(),
        true,
        key.statement(PREIMAGE),
        key.prove(PREIMAGE, rng),
    )
}

/// [`one_private_preimage`] guarded off: no key, no proof, nothing to check.
pub fn guarded_off_preimage() -> ProofPreimage {
    one_private_preimage(Fr::from(0), false, Fr::from(0), vec![])
}

/// Runs `check_with_inner_vks` and returns its error message.
pub fn expect_check_err(
    ir: &IrSource,
    preimage: &ProofPreimage,
    keys: &[Option<VerifyingKey<Fq, KZG>>],
) -> String {
    match ir.check_with_inner_vks(preimage, keys) {
        Ok(_) => panic!("check unexpectedly succeeded"),
        Err(e) => format!("{e:#}"),
    }
}
