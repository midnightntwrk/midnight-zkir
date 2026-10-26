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

#[path = "common/mod.rs"]
mod common;
#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use std::borrow::Cow;
use std::collections::HashMap;
use std::sync::Arc;

use common::TestResolver;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{AssertionInstructions, AssignmentInstructions},
    types::AssignedNative,
    verifier::vk_hash,
};
use midnight_curves::Bls12;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk,
    poly::kzg::params::ParamsKZG,
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{KZG, MidnightVK, Relation, ZkStdLib, ZkStdLibArch, optimal_k, setup_vk};
use midnight_zkir::{
    Identifier, IrSource, Preprocessed,
    ir_instructions::{encode::encode_offcircuit, unbound_vk::INNER_ARCH},
    ir_types::{InnerVk, IrValue},
};
use rand::SeedableRng;
use rand_chacha::ChaCha20Rng;
use transient_crypto::curve::{Fr, outer};
use transient_crypto::proofs::{KeyLocation, ProofPreimage, Zkir};
use verify_proof_common::srs;

/// An inner circuit with every chip enabled, whose fixed columns depend on `c`.
#[derive(Clone)]
struct Inner(u64);

impl Relation for Inner {
    type Instance = ();
    type Witness = ();
    type Error = plonk::Error;

    fn format_instance(_: &()) -> Result<Vec<outer::Scalar>, plonk::Error> {
        Ok(vec![])
    }

    fn circuit(
        &self,
        std: &ZkStdLib,
        layouter: &mut impl Layouter<outer::Scalar>,
        _: Value<()>,
        _: Value<()>,
    ) -> Result<(), plonk::Error> {
        let c = outer::Scalar::from(self.0);
        let x: AssignedNative<_> = std.assign_fixed(layouter, c)?;
        std.assert_equal_to_fixed(layouter, &x, c)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        INNER_ARCH
    }

    fn write_relation<W: std::io::Write>(&self, _: &mut W) -> std::io::Result<()> {
        unimplemented!()
    }

    fn read_relation<R: std::io::Read>(_: &mut R) -> std::io::Result<Self> {
        unimplemented!()
    }
}

fn inner_vk(c: u64) -> MidnightVK<KZG> {
    let relation = Inner(c);
    let params = ParamsKZG::<Bls12>::unsafe_setup(
        optimal_k(&relation),
        ChaCha20Rng::from_seed([c as u8; 32]),
    );
    setup_vk::<_, KZG>(&params, &relation)
}

/// The private transcript carrying `vk`, packed as a `Bytes` value.
fn transcript(vk: &MidnightVK<KZG>) -> Vec<Fr> {
    let bytes = vk.vk().to_bytes(SerdeFormat::Processed);
    (encode_offcircuit(&IrValue::Bytes(bytes)).into_iter())
        .map(|x| x.try_into().unwrap())
        .collect()
}

fn preimage(hash: Fr, private_transcript: Vec<Fr>) -> ProofPreimage {
    ProofPreimage {
        binding_input: 42.into(),
        communications_commitment: None,
        inputs: vec![hash],
        private_transcript,
        public_transcript_inputs: vec![],
        public_transcript_outputs: vec![],
        inner_proofs: vec![],
        key_location: KeyLocation(Cow::Borrowed("builtin")),
    }
}

#[actix_rt::test]
async fn test_bind_unbound_vk() {
    let vk = inner_vk(1);
    let other_vk = inner_vk(2);
    assert_eq!(vk.k(), other_vk.k());
    let hash = Fr(vk_hash::<PoseidonChip<outer::Scalar>, outer::Scalar, KZG>(
        vk.vk(),
    ));

    let ir_raw = format!(
        r#"{{
           "version": {{ "major": 4, "minor": 0 }},
           "inputs": [
              {{ "name": "%hash", "type": "Scalar<BLS12-381>" }}
           ],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": [
               {{ "op": "assign_unbound_vk", "k": {}, "output": "%vk" }},
               {{ "op": "bind_vk", "vk": "%vk", "hash": "%hash" }}
           ]
        }}"#,
        vk.k()
    );
    let ir = IrSource::load(ir_raw.as_bytes()).unwrap();

    // Off-circuit, the key must match the hash.
    assert!(preimage(hash, transcript(&other_vk)).check(&ir).is_err());

    let (pk, ir_vk) = ir.keygen(srs()).await.unwrap();
    let resolver = TestResolver {
        pk: pk.clone(),
        vk: ir_vk.clone(),
        ir: ir.clone(),
    };
    let (proof, _) = preimage(hash, transcript(&vk))
        .prove::<IrSource>(&mut ChaCha20Rng::from_seed([42; 32]), srs(), &resolver)
        .await
        .unwrap();
    ir_vk
        .verify(&srs().verifier, &proof, [42.into()].into_iter())
        .unwrap();

    // In-circuit, a malicious prover cannot witness a key that does not match
    // the hash (the honest key is the control).
    for (witnessed_vk, is_valid) in [(&vk, true), (&other_vk, false)] {
        let preproc = Preprocessed {
            memory: HashMap::from([
                (Identifier("%hash".into()), IrValue::Native(hash)),
                (
                    Identifier("%vk".into()),
                    IrValue::UnboundVk(InnerVk(Arc::new(witnessed_vk.vk().clone()))),
                ),
            ]),
            pis: vec![42.into()],
            pi_skips: vec![],
            binding_input: 42.into(),
            comm_comm: None,
            inner_proofs: vec![],
        };
        let proof = ir
            .prove_unchecked(
                &mut ChaCha20Rng::from_seed([42; 32]),
                srs(),
                pk.clone(),
                preproc,
            )
            .await;
        let verify =
            proof.and_then(|proof| ir_vk.verify(&srs().verifier, &proof, [42.into()].into_iter()));
        assert_eq!(verify.is_ok(), is_valid);
    }
}
