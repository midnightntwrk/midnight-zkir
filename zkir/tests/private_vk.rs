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

//! Tests for verifying inner proofs under private verifying keys that build no
//! outer circuit: the IR format and its validation, the off-circuit checks
//! `check_with_inner_vks` runs on the keys it is handed, the `vk_id` identity,
//! and fixed keys named by their `vk_id`. End-to-end tests are in
//! `private_vk_e2e.rs`.

#[path = "common/private_vk.rs"]
mod private_vk_common;
#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use midnight_circuits::hash::poseidon::PoseidonChip;
use midnight_circuits::instructions::hash::HashCPU;
use midnight_circuits::verifier::vk_hash;
use midnight_curves::Fq;
use midnight_proofs::utils::SerdeFormat;
use midnight_zk_stdlib::{KZG, MidnightVK};
use midnight_zkir::{IrSource, vk_id};
use serialize::{Deserializable, Serializable};
use sha2::Digest;
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{InnerProofWitness, Zkir};

use crate::private_vk_common::{
    NB_PUBLIC_INPUTS, PREIMAGE, PrivateKey, bound_vk, expect_check_err, fixed_vk,
    guarded_off_preimage, honest_preimage, imm, inner_k, input, key_a, key_b, load,
    one_private_preimage, one_private_verification, private_verification,
    private_verification_with,
};
use crate::verify_proof_common::{
    SingleScalarRelation, inner_setup_at, inner_setup_for, preimage_with, test_rng, with_vks,
};

/// The `vk_id` of the [`SingleScalarRelation`] key that [`inner_setup_for`]
/// generates from the fixed test SRS.
///
/// This is a golden value: it changes exactly when the definition of `vk_id`,
/// or anything it hashes (midnight-proofs' `transcript_repr`, the key's
/// commitments, the domain tag), changes. When this test fails, every
/// published key identity has changed with it: make sure that is intended,
/// then record the new value.
const GOLDEN_VK_ID: Option<&str> =
    Some("0x01a0e1b339ac482df9b85f066bf0e191fb2fa08cda8958e6e277612cf361a248");

// ---------------------------------------------------------------------------
// IR format and validation
// ---------------------------------------------------------------------------

/// The private-key instructions survive the JSON text format and the binary
/// format.
#[test]
fn private_vk_ir_round_trips() {
    let ir = one_private_verification(10);

    let json = serde_json::to_string_pretty(&ir).expect("IrSource serializes");
    for expected in [
        r#""op": "assign_unbound_vk""#,
        r#""op": "bind_vk""#,
        r#""k": 10"#,
        r#""nb_public_inputs": 1"#,
        r#""bound": "%b_0""#,
    ] {
        assert!(json.contains(expected), "{expected} missing:\n{json}");
    }
    let reloaded: IrSource = serde_json::from_str(&json).expect("re-serialized IR must parse");
    assert_eq!(as_json(&reloaded), as_json(&ir));

    let mut bytes = Vec::new();
    Serializable::serialize(&ir, &mut bytes).expect("IrSource serializes");
    assert_eq!(bytes.len(), ir.serialized_size());
    let read: IrSource = Deserializable::deserialize(&mut &bytes[..], 0).expect("deserialize");
    assert_eq!(as_json(&read), as_json(&ir));
}

/// A fixed key is named by its `vk_id` in the text format.
#[test]
fn fixed_vk_ir_round_trips() {
    let id = Fr::from(0x1234u64);
    let ir = load(
        "",
        &format!(
            r#"{{ "op": "inner_proof", "guard": "0x00", "output": "%p" }},
               {{ "op": "prepare_verification", "guard": "0x00", "vk": {vk},
                  "instance": ["0x7b"], "proof": "%p", "output": "%a" }},
               {{ "op": "verify_accumulator", "input": "%a" }}"#,
            vk = fixed_vk(id),
        ),
    );
    let json = serde_json::to_string_pretty(&ir).expect("IrSource serializes");
    assert!(
        json.contains(&format!(r#""fixed": {}"#, imm(id))),
        "fixed vk_id missing:\n{json}"
    );
    assert!(!json.contains("vk_hash"), "vk_hash is gone:\n{json}");
}

/// `assign_unbound_vk`, `bind_vk` and `prepare_verification` share one guard,
/// as `inner_proof` and `prepare_verification` do: a key witnessed, bound or
/// used under a different condition than the proof is rejected.
#[test]
fn guards_must_match_from_assignment_to_preparation() {
    let inputs = [input("%h"), input("%g"), input("%g2")].join(", ");
    let check = |guards: [&str; 3]| {
        let ir = load(
            &inputs,
            &private_verification_with(0, guards, inner_k(), 1, r#""%h""#, &[r#""0x7b""#]),
        );
        let mut preimage = guarded_off_preimage();
        preimage.inputs = vec![Fr::from(0); 3];
        ir.check_with_inner_vks(&preimage, &[None])
            .map_err(|e| format!("{e:#}"))
    };

    check(["%g", "%g", "%g"]).expect("matching guards are accepted");
    for guards in [
        ["%g2", "%g", "%g"],
        ["%g", "%g2", "%g"],
        ["%g", "%g", "%g2"],
    ] {
        let err = check(guards).expect_err("mismatched guards must be rejected");
        assert!(err.contains("guard"), "{guards:?}: {err}");
    }
}

/// `prepare_verification` takes a key only once it is bound: an `UnboundVk`, or
/// a plain value, is rejected.
#[test]
fn prepare_verification_needs_a_bound_key() {
    let instructions = |vk: &str| {
        format!(
            r#"{{ "op": "inner_proof", "guard": "0x00", "output": "%p" }},
               {{ "op": "assign_unbound_vk", "guard": "0x00", "k": {k}, "nb_public_inputs": 1,
                  "output": "%u" }},
               {{ "op": "bind_vk", "guard": "0x00", "vk": "%u", "hash": "%h", "output": "%b" }},
               {{ "op": "prepare_verification", "guard": "0x00", "vk": {vk},
                  "instance": ["0x7b"], "proof": "%p", "output": "%a" }},
               {{ "op": "verify_accumulator", "input": "%a" }}"#,
            k = inner_k(),
        )
    };
    let check = |vk: &str| {
        let ir = load(&input("%h"), &instructions(vk));
        let mut preimage = preimage_with(vec![InnerProofWitness::Direct(vec![])]);
        preimage.inputs = vec![Fr::from(0)];
        ir.check_with_inner_vks(&preimage, &[None])
            .map_err(|e| format!("{e:#}"))
    };

    check(&bound_vk("%b")).expect("a bound key is accepted");
    for vk in [bound_vk("%u"), bound_vk("%h")] {
        let err = check(&vk).expect_err("only a BoundVk can verify a proof");
        assert!(err.contains("BoundVk"), "{vk}: {err}");
    }
}

/// One bound key can verify several proofs.
#[test]
fn a_bound_key_verifies_several_proofs() {
    let ir = load(
        &input("%h"),
        &format!(
            r#"{{ "op": "inner_proof", "guard": "0x00", "output": "%p_0" }},
               {{ "op": "inner_proof", "guard": "0x00", "output": "%p_1" }},
               {{ "op": "assign_unbound_vk", "guard": "0x00", "k": {k}, "nb_public_inputs": 1,
                  "output": "%u" }},
               {{ "op": "bind_vk", "guard": "0x00", "vk": "%u", "hash": "%h", "output": "%b" }},
               {{ "op": "prepare_verification", "guard": "0x00", "vk": {vk},
                  "instance": ["0x7b"], "proof": "%p_0", "output": "%a_0" }},
               {{ "op": "prepare_verification", "guard": "0x00", "vk": {vk},
                  "instance": ["0x7c"], "proof": "%p_1", "output": "%a_1" }},
               {{ "op": "verify_accumulator", "input": "%a_0" }},
               {{ "op": "verify_accumulator", "input": "%a_1" }}"#,
            k = inner_k(),
            vk = bound_vk("%b"),
        ),
    );
    let mut preimage = preimage_with(vec![
        InnerProofWitness::Direct(vec![]),
        InnerProofWitness::Direct(vec![]),
    ]);
    preimage.inputs = vec![Fr::from(0)];
    ir.check_with_inner_vks(&preimage, &[None])
        .expect("one bound key, two proofs");
    assert_eq!(ir.inner_vk_slots(), 1);
    assert_eq!(ir.accumulator_count(), 2);
}

/// The key's declared public inputs, which its `vk_id` covers, must match the
/// instance it verifies.
#[test]
fn instance_length_must_match_the_keys_public_inputs() {
    let check = |nb_public_inputs: usize| {
        let ir = load(
            &[input("%h"), input("%g")].join(", "),
            &private_verification_with(
                0,
                ["%g"; 3],
                inner_k(),
                nb_public_inputs,
                r#""%h""#,
                &[r#""0x7b""#, r#""0x7c""#],
            ),
        );
        let mut preimage = guarded_off_preimage();
        preimage.inputs = vec![Fr::from(0); 2];
        ir.check_with_inner_vks(&preimage, &[None])
            .map_err(|e| format!("{e:#}"))
    };

    check(2).expect("matching instance length is accepted");
    let err = check(1).expect_err("a mismatched instance length must be rejected");
    assert!(err.contains("public inputs"), "{err}");
}

/// There is one key slot per `assign_unbound_vk`, whatever its guard.
#[test]
fn inner_vk_slots_counts_assign_unbound_vk_instructions() {
    let k = inner_k();
    let ir = load(
        &[input("%h"), input("%g")].join(", "),
        &[
            private_verification(0, "%g", k, r#""%h""#, "\"0x7b\""),
            private_verification(1, "0x00", k, r#""%h""#, "\"0x7b\""),
            private_verification(2, "0x01", k, r#""%h""#, "\"0x7b\""),
        ]
        .join(",\n"),
    );
    assert_eq!(ir.inner_vk_slots(), 3);
}

// ---------------------------------------------------------------------------
// Off-circuit checks on the supplied keys
// ---------------------------------------------------------------------------

/// The control for the tests below: the key the hash names, with a proof
/// under it, passes.
#[test]
fn check_accepts_the_key_its_hash_names() {
    let key = key_a();
    let ir = one_private_verification(key.k());
    let preimage = honest_preimage(key, &mut test_rng());
    ir.check_with_inner_vks(&preimage, &[Some(key.plonk_vk())])
        .expect("the named key is accepted");
}

/// A key whose `vk_id` is not the hash `bind_vk` binds it to is rejected.
#[test]
fn check_rejects_a_key_that_does_not_match_the_hash() {
    let (a, b) = (key_a(), key_b());
    let ir = one_private_verification(a.k());
    let preimage = honest_preimage(a, &mut test_rng());
    let err = expect_check_err(&ir, &preimage, &[Some(b.plonk_vk())]);
    assert!(err.contains("hash"), "{err}");
}

/// A key of another shape than `INNER_ARCH` is an error, not a panic.
#[actix_rt::test]
async fn check_rejects_a_key_of_another_shape() {
    let k = inner_k();
    let (_, _, blob) = inner_setup_at::<SingleScalarRelation>("other shape", k).await;
    let other_shape = MidnightVK::<KZG>::read(&mut &blob[..], SerdeFormat::Processed)
        .expect("read key")
        .vk()
        .clone();

    let ir = one_private_verification(k);
    let preimage = one_private_preimage(Fr::from(0), true, Fr::from(0), vec![]);
    let err = expect_check_err(&ir, &preimage, &[Some(other_shape)]);
    assert!(err.contains("constraint system"), "{err}");
}

/// A key of another size than the instruction's `2^k` is rejected.
#[test]
fn check_rejects_a_key_of_another_size() {
    let a = key_a();
    let larger = PrivateKey::at(1, a.k() + 1);
    let ir = one_private_verification(a.k());
    let preimage = one_private_preimage(larger.id(), true, Fr::from(0), vec![]);
    let err = expect_check_err(&ir, &preimage, &[Some(larger.plonk_vk())]);
    assert!(err.contains("size"), "{err}");
}

/// Keys are handed over one per `assign_unbound_vk`, in instruction order.
#[test]
fn keys_are_consumed_in_instruction_order() {
    let mut rng = test_rng();
    let small = key_a();
    let large = PrivateKey::at(1, small.k() + 1);

    let ir = load(
        &[input("%h_0"), input("%h_1")].join(", "),
        &[
            private_verification(
                0,
                "0x01",
                small.k(),
                r#""%h_0""#,
                &imm(small.statement(PREIMAGE)),
            ),
            private_verification(
                1,
                "0x01",
                large.k(),
                r#""%h_1""#,
                &imm(large.statement(PREIMAGE)),
            ),
        ]
        .join(",\n"),
    );
    let mut preimage = preimage_with(vec![
        InnerProofWitness::Direct(small.prove(PREIMAGE, &mut rng)),
        InnerProofWitness::Direct(large.prove(PREIMAGE, &mut rng)),
    ]);
    preimage.inputs = vec![small.id(), large.id()];

    ir.check_with_inner_vks(&preimage, &[Some(small.plonk_vk()), Some(large.plonk_vk())])
        .expect("keys in instruction order are accepted");
    expect_check_err(
        &ir,
        &preimage,
        &[Some(large.plonk_vk()), Some(small.plonk_vk())],
    );
}

/// Exactly one key slot per `assign_unbound_vk` must be supplied.
#[test]
fn key_count_must_match_the_slots() {
    let key = key_a();
    let ir = one_private_verification(key.k());
    let preimage = honest_preimage(key, &mut test_rng());

    for keys in [vec![], vec![Some(key.plonk_vk()), Some(key.plonk_vk())]] {
        let err = expect_check_err(&ir, &preimage, &keys);
        assert!(err.contains("verifying key"), "{} keys: {err}", keys.len());
    }
}

/// Guarded off, a slot needs no key, no proof and no matching hash: zkir uses
/// its own dummy key. Guarded on, a missing key is an error.
#[test]
fn a_guarded_off_slot_needs_no_key() {
    let ir = one_private_verification(inner_k());

    let off = one_private_preimage(Fr::from(0xdead), false, Fr::from(0), vec![]);
    ir.check_with_inner_vks(&off, &[None])
        .expect("guarded off, nothing is needed");

    let on = honest_preimage(key_a(), &mut test_rng());
    let err = expect_check_err(&ir, &on, &[None]);
    assert!(err.contains("verifying key"), "{err}");
}

// ---------------------------------------------------------------------------
// The `vk_id` identity
// ---------------------------------------------------------------------------

/// `vk_id` of a fixed key is a known value. See [`GOLDEN_VK_ID`].
#[actix_rt::test]
async fn vk_id_matches_the_golden_value() {
    let (_, _, blob) = inner_setup_for::<SingleScalarRelation>("golden").await;
    let vk = MidnightVK::<KZG>::read(&mut &blob[..], SerdeFormat::Processed).expect("read key");
    let id = imm(vk_id(vk.vk(), 1));

    let Some(golden) = GOLDEN_VK_ID else {
        panic!("no golden vk_id recorded yet; the current value is {id}");
    };
    assert_eq!(
        id,
        format!("\"{golden}\""),
        "vk_id changed: every published key identity has changed with it"
    );
}

/// `vk_id` is domain-separated: it is neither midnight-zk's raw `vk_hash` nor
/// an untagged Poseidon hash of the same data, so a `vk_id` cannot be confused
/// with another Poseidon value.
#[test]
fn vk_id_is_domain_separated() {
    let vk = key_a().vk.vk();
    let raw = vk_hash::<PoseidonChip<Fq>, Fq, KZG>(vk);
    let untagged =
        <PoseidonChip<Fq> as HashCPU<Fq, Fq>>::hash(&[Fq::from(NB_PUBLIC_INPUTS as u64), raw]);

    let id = vk_id(vk, NB_PUBLIC_INPUTS);
    assert_ne!(id, Fr(raw));
    assert_ne!(id, Fr(untagged));
}

/// `vk_id` covers the number of public inputs, and tells keys apart.
#[test]
fn vk_id_identifies_the_key_and_its_public_inputs() {
    let (a, b) = (key_a().vk.vk(), key_b().vk.vk());
    assert_eq!(vk_id(a, 1), vk_id(a, 1));
    assert_ne!(vk_id(a, 1), vk_id(a, 2));
    assert_ne!(vk_id(a, 1), vk_id(b, 1));
}

// ---------------------------------------------------------------------------
// Fixed keys, named by `vk_id`
// ---------------------------------------------------------------------------

/// A fixed key is named by its `vk_id`, and the same key bound privately is
/// bound to the same value: one identity, whichever path verifies it.
#[test]
fn one_identity_for_fixed_and_private_keys() {
    let key = key_a();
    let proof = key.prove(PREIMAGE, &mut test_rng());

    let fixed = with_vks(load("", &fixed_verification(key)), vec![key.blob()]);
    let preimage = preimage_with(vec![InnerProofWitness::Direct(proof.clone())]);
    fixed
        .check(&preimage)
        .expect("the fixed key is found by its vk_id");

    let private = one_private_verification(key.k());
    let preimage = one_private_preimage(key.id(), true, key.statement(PREIMAGE), proof);
    private
        .check_with_inner_vks(&preimage, &[Some(key.plonk_vk())])
        .expect("the private key binds to the same vk_id");
}

/// A fixed key named by the SHA-256 of its blob, as before, is not found.
#[test]
fn fixed_key_named_by_sha256_is_rejected() {
    let key = key_a();
    let blob = key.blob();
    let sha = Fr::from_le_bytes(&sha2::Sha256::digest(&blob)[..31]).expect("31 bytes fit");

    // The digest truncated to fit a field element; either way it is not the
    // key's vk_id, so the lookup fails.
    let ir = with_vks(load("", &fixed_verification_as(sha, key)), vec![blob]);
    let preimage = preimage_with(vec![InnerProofWitness::Direct(
        key.prove(PREIMAGE, &mut test_rng()),
    )]);
    let err = match ir.check(&preimage) {
        Ok(_) => panic!("check unexpectedly succeeded"),
        Err(e) => format!("{e:#}"),
    };
    assert!(err.contains("no verifying key"), "{err}");
}

/// Keys in the fixed-key side-table are indexed by `vk_id`: two blobs of the
/// same key are a duplicate.
#[test]
fn duplicate_fixed_key_is_rejected_by_vk_id() {
    let key = key_a();
    let ir = with_vks(
        load("", &fixed_verification(key)),
        vec![key.blob(), key.blob()],
    );
    let preimage = preimage_with(vec![InnerProofWitness::Direct(vec![])]);
    let err = match ir.check(&preimage) {
        Ok(_) => panic!("check unexpectedly succeeded"),
        Err(e) => format!("{e:#}"),
    };
    assert!(err.contains("duplicate"), "{err}");
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Verifies a proof of knowledge of [`PREIMAGE`] under the fixed `key`.
fn fixed_verification(key: &PrivateKey) -> String {
    fixed_verification_as(key.id(), key)
}

/// [`fixed_verification`], naming the key by `id`.
fn fixed_verification_as(id: Fr, key: &PrivateKey) -> String {
    format!(
        r#"{{ "op": "inner_proof", "guard": "0x01", "output": "%p" }},
           {{ "op": "prepare_verification", "guard": "0x01", "vk": {vk},
              "instance": [{statement}], "proof": "%p", "output": "%a" }},
           {{ "op": "verify_accumulator", "input": "%a" }}"#,
        vk = fixed_vk(id),
        statement = imm(key.statement(PREIMAGE)),
    )
}

fn as_json(ir: &IrSource) -> serde_json::Value {
    serde_json::to_value(ir).expect("IrSource serializes")
}
