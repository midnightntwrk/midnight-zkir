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

//! Tests for the `inner_proof` / `prepare_verification` instruction pair that build no
//! outer circuit: the text format, IR serialization, and the checks `check`
//! runs on the IR and its proof witnesses. End-to-end tests are in
//! `verify_proof_e2e.rs`.

#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use midnight_zkir::IrSource;
use midnight_zkir::ir_instructions::prepare_verification::prepare_verification_offcircuit;
use serialize::{Deserializable, Serializable, tagged_deserialize, tagged_serialize};
use transient_crypto::proofs::{InnerProofWitness, ProofPreimage, Zkir};

use crate::verify_proof_common::{
    load_ir, load_vk, preimage_with, scalar_inner_proof, scalar_vk_blob, stub_vk_ref, test_rng,
    vk_ref, with_vks,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Canonical, hash-only IR: `%p_0` is bound to the inner proof, the inner
/// statement is the single public input `%v_0`, and the instruction stores just
/// the VK's `vk_id`. Neither the full VK nor the proof appears in the text — both
/// are supplied out-of-band.
///
/// The second `prepare_verification` shows the other shape of the same operator: a
/// constant guard, always `0x01`, i.e. verify unconditionally.
const VERIFY_PROOF_IR: &str = r#"{
   "version": { "major": 4, "minor": 0 },
   "inputs": [
      { "name": "%v_0", "type": "Scalar<BLS12-381>" },
      { "name": "%g", "type": "Scalar<BLS12-381>" }
   ],
   "outputs": [],
   "do_communications_commitment": false,
   "instructions": [
       {
           "op": "load_constant",
           "type": "BoundVk",
           "encoding": ["0x2a"],
           "output": "%k"
       },
       {
           "op": "inner_proof",
           "guard": "%g",
           "output": "%p_0"
       },
       {
           "op": "prepare_verification",
           "guard": "%g",
           "vk": "%k",
           "instance": ["%v_0"],
           "proof": "%p_0",
           "output": "%a_0"
       },
       { "op": "verify_accumulator", "input": "%a_0" },
       {
           "op": "inner_proof",
           "guard": "0x01",
           "output": "%p_1"
       },
       {
           "op": "prepare_verification",
           "guard": "0x01",
           "vk": "%k",
           "instance": ["%v_0"],
           "proof": "%p_1",
           "output": "%a_1"
       },
       { "op": "verify_accumulator", "input": "%a_1" }
   ]
}"#;

/// Stub VK blobs of different lengths. They are never parsed as keys.
const VK_BLOB_A: [u8; 32] = [0xaa; 32];

const VK_BLOB_B: [u8; 48] = [0xbb; 48];

/// The size of the real keys tests resolve but verify nothing under.
const REAL_K: u8 = 6;

/// A lone `inner_proof` binding.
const BIND_ONE: &str = r#"{ "op": "inner_proof", "guard": "0x01", "output": "%p_0" }"#;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// `accumulator_count()` is one per `verify_accumulator` instruction, whatever
/// the key or guard of the `prepare_verification` it verifies.
#[test]
fn accumulator_count_tracks_verify_proof_instructions() {
    assert_eq!(
        count(r#"{ "op": "impact", "guard": "0x01", "inputs": ["0x2a"] }"#),
        0
    );

    // A binding alone verifies nothing.
    assert_eq!(
        count(r#"{ "op": "inner_proof", "guard": "0x01", "output": "%p_0" }"#),
        0
    );

    assert_eq!(count(&bind_and_verify_one(&stub_ref(&VK_BLOB_A))), 1);
    assert_eq!(
        count(&bind_and_verify(&[
            stub_ref(&VK_BLOB_A),
            stub_ref(&VK_BLOB_B)
        ])),
        2
    );

    // Two instructions sharing one key still expose two accumulators.
    assert_eq!(
        count(&bind_and_verify(&[
            stub_ref(&VK_BLOB_A),
            stub_ref(&VK_BLOB_A)
        ])),
        2,
        "the count is per instruction, not per distinct key"
    );

    let interleaved = format!(
        "{},\n{},\n{}",
        guarded_pair(0, "0x01", &VK_BLOB_A),
        r#"{ "op": "impact", "guard": "0x01", "inputs": ["0x2a", "0x2b"] }"#,
        guarded_pair(1, "0x01", &VK_BLOB_B),
    );
    assert_eq!(
        count(&interleaved),
        2,
        "an Impact contributes no accumulator"
    );

    // The count must be known at keygen, before any witness exists, so a
    // guarded-off `prepare_verification` still counts.
    for guard in ["0x01", "0x00", "%v_0"] {
        assert_eq!(
            count(&guarded_pair(0, guard, &VK_BLOB_A)),
            1,
            "guard {guard}: a guarded-off prepare_verification still exposes the trivial accumulator"
        );
    }

    let mixed = format!(
        "{},\n{}",
        guarded_pair(0, "0x01", &VK_BLOB_A),
        guarded_pair(1, "0x00", &VK_BLOB_B),
    );
    assert_eq!(
        count(&mixed),
        2,
        "the split must not depend on which branch the prover takes"
    );

    let accumulated = format!(
        "{},\n{}",
        bind_and_prepare(&[stub_ref(&VK_BLOB_A), stub_ref(&VK_BLOB_B)]),
        r#"{ "op": "accumulate", "inputs": ["%a_0", "%a_1"], "output": "%a" },
           { "op": "verify_accumulator", "input": "%a" }"#,
    );
    assert_eq!(
        count(&accumulated),
        1,
        "accumulated accumulators are exposed once"
    );

    let ir_hash_only: IrSource = ir(&bind_and_verify_one(&stub_ref(&VK_BLOB_A)));
    let mut ir_with_keys = ir_hash_only.clone();
    ir_with_keys.inner_vks = vec![VK_BLOB_A.to_vec()];
    assert_eq!(
        ir_hash_only.accumulator_count(),
        ir_with_keys.accumulator_count(),
        "resolving the side-table must not change the exposed shape"
    );
}

/// The same VK blob listed twice in `inner_vks` is rejected, even though
/// an instruction uses it. The side-table is indexed by `vk_id`, so the second
/// copy could never be resolved.
#[test]
fn duplicate_vk_in_side_table_is_rejected() {
    let blob = scalar_vk_blob(REAL_K);
    let duplicated = ir_with_vks(
        &bind_and_verify_one(&vk_ref(&blob)),
        vec![blob.clone(), blob],
    );
    let err = expect_check_err(&duplicated, preimage(1));
    assert!(err.contains("duplicate verifying key"), "got: {err}");
}

/// The VK side-table survives a binary round-trip, and loads from inline JSON.
#[test]
fn the_vk_side_table_round_trips() {
    let ir = ir_with_vks(BIND_ONE, vec![VK_BLOB_A.to_vec()]);
    let back = read(&write(&ir).expect("an IR with a side-table must write"));
    assert_eq!(back, ir, "the IR must round-trip");

    let inline = IrSource::load(ir_with_side_table().as_bytes()).expect("inline side-table");
    assert_eq!(inline.inner_vks, vec![vec![0u8, 1, 2]]);
}

/// `vk` and `inner_vks` survive JSON and binary round-trips, in
/// order.
#[test]
fn ir_round_trip_preserves_vks_in_order() {
    let ir = ir_with_vks(
        &instructions(),
        vec![VK_BLOB_A.to_vec(), VK_BLOB_B.to_vec()],
    );

    let json = serde_json::to_string(&ir).expect("serializes");
    assert!(json.contains("inner_vks"), "{json}");
    let back: IrSource = serde_json::from_str(&json).expect("parses back");
    assert_eq!(back, ir);

    let mut bytes = Vec::new();
    tagged_serialize(&ir, &mut bytes).expect("serializes");
    let back: IrSource = tagged_deserialize(&bytes[..]).expect("parses back");
    assert_eq!(back, ir);
}

/// Malformed proof bytes make `check` return an error rather than panic.
/// Trailing bytes after a valid proof are ignored.
#[actix_rt::test]
async fn malformed_proof_witness_is_rejected() {
    // A proof of 123, the instance `bind_and_verify_one` verifies against.
    let inner = scalar_inner_proof(&mut test_rng()).await;
    let ir = ir_with_vks(
        &bind_and_verify_one(&vk_ref(&inner.vk_blob)),
        vec![inner.vk_blob.clone()],
    );
    let check =
        |witness: Vec<u8>| ir.check(&preimage_with(vec![InnerProofWitness::Direct(witness)]));

    let cases: Vec<(&str, Vec<u8>)> = vec![
        ("empty", Vec::new()),
        ("short nonsense", b"not a proof".to_vec()),
        ("right length, wrong bytes", vec![0xff; inner.proof.len()]),
        (
            "truncated real proof",
            inner.proof[..inner.proof.len() / 2].to_vec(),
        ),
    ];

    for (label, witness) in cases {
        match check(witness) {
            Ok(_) => panic!("{label}: malformed bytes were accepted as a proof witness"),
            Err(e) => println!("{label}: rejected -- {e:#}"),
        }
    }

    check(inner.proof.clone()).expect("a genuine inner proof must pass off-circuit preparation");

    // The transcript reader stops once it has read the proof, so trailing
    // bytes are accepted. They must not change the accumulator.
    let mut padded = inner.proof.clone();
    padded.extend_from_slice(b"trailing junk");
    check(padded.clone()).expect("trailing bytes are ignored by the transcript reader");

    let from_real = prepare_verification_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
        .expect("preparation of the real proof");
    let from_padded = prepare_verification_offcircuit(&inner.vk_blob, &inner.pis, &padded, true)
        .expect("preparation of the padded proof");
    assert_eq!(
        from_real, from_padded,
        "trailing bytes must not change the accumulator"
    );
}

/// Proof witnesses and side-table keys the circuit never uses are rejected.
#[test]
fn surplus_witness_or_vk_is_rejected() {
    let err = expect_check_err(&ir(""), preimage(1));
    assert!(err.contains("proof witnesses"), "got: {err}");

    let blob = scalar_vk_blob(REAL_K);
    let err = expect_check_err(&ir_with_vks("", vec![blob.clone()]), preimage(0));
    assert!(
        err.contains("inner_vks") && err.contains("used"),
        "got: {err}"
    );

    // Guarded off, so the key is never used.
    let paired = ir_with_vks(&bind_and_verify_off(&[vk_ref(&blob)]), vec![blob]);
    let err = expect_check_err(&paired, preimage(2));
    assert!(err.contains("proof witnesses"), "got: {err}");

    ir("").check(&preimage(0)).expect("empty circuit");
    paired
        .check(&preimage(1))
        .expect("one binding, one witness");
}

/// The `inner_proof` / `prepare_verification` text format round-trips through JSON.
///
/// `inner_proof` binds the next inner proof witness to a name, which
/// `prepare_verification` takes as its `proof` input. `vk` names a key in the
/// `inner_vks` side-table by its `vk_id`; the text stores only the `vk_id`.
/// Guards are ordinary operands, a variable or a `0x` immediate. The `vk_id`
/// here is fake: nothing is verified.
#[test]
fn verify_proof_text_format_roundtrips() {
    let ir =
        IrSource::load(VERIFY_PROOF_IR.as_bytes()).expect("prepare_verification IR must parse");

    // A hash-only IR carries no VK bytes.
    assert!(
        ir.inner_vks.is_empty(),
        "hash-only IR should not carry VK blobs"
    );

    // Re-serialize so the exact canonical instruction shape is visible with
    // `cargo test -- --nocapture`.
    let json = serde_json::to_string_pretty(&ir).expect("IrSource serializes");
    println!("{json}");

    // Both instructions survive the round-trip, the proof flows from one to the
    // other by name, the VK hash stays a `0x` hex string, and the empty VK
    // side-table is omitted.
    assert!(json.contains("inner_proof"), "op tag missing:\n{json}");
    assert!(
        json.contains("prepare_verification"),
        "op tag missing:\n{json}"
    );
    assert!(json.contains("%p_0"), "proof operand missing:\n{json}");
    assert!(
        json.contains(r#""type": "BoundVk""#) && json.contains(r#""0x2a""#),
        "vk_id missing:\n{json}"
    );
    assert!(
        json.contains(r#""vk": "%k""#),
        "key operand missing:\n{json}"
    );
    assert!(json.contains("%v_0"), "instance operand missing:\n{json}");

    // Both guard forms survive as operands: a variable stays a variable, and a
    // constant round-trips as the canonical `0x`-hex immediate.
    assert!(
        json.contains("\"guard\": \"%g\""),
        "variable guard missing:\n{json}"
    );
    assert!(
        json.contains("\"guard\": \"0x01\""),
        "constant guard missing:\n{json}"
    );
    assert!(
        !json.contains("inner_vks"),
        "empty VK side-table should be omitted:\n{json}"
    );
}

/// Every accumulator must reach exactly one `accumulate` or
/// `verify_accumulator`: a dropped one is an unchecked proof.
#[test]
fn every_accumulator_is_verified_exactly_once() {
    let prepared = bind_and_prepare(&[stub_ref(&VK_BLOB_A)]);
    let err = expect_check_err(&ir(&prepared), preimage(1));
    assert!(err.contains("never verified"), "got: {err}");

    let verify_one = bind_and_verify_one(&stub_ref(&VK_BLOB_A));
    let twice = format!(r#"{verify_one},{{ "op": "verify_accumulator", "input": "%a_0" }}"#);
    let err = expect_check_err(&ir(&twice), preimage(1));
    assert!(err.contains("not an unconsumed accumulator"), "got: {err}");

    let witnessed =
        r#"{ "op": "private_input", "guard": "0x00", "type": "Accumulator", "output": "%c" }"#;
    let err = expect_check_err(&ir(witnessed), preimage(0));
    assert!(err.contains("never verified"), "got: {err}");

    // Neither `%x` nor `%y` was produced, so `%x` cannot feed itself.
    let self_fed = r#"{ "op": "accumulate", "inputs": ["%x", "%y"], "output": "%x" }"#;
    let err = expect_check_err(&ir(self_fed), preimage(0));
    assert!(err.contains("not an unconsumed accumulator"), "got: {err}");

    // An accumulator input must be verified too.
    let input = load_ir(r#"{ "name": "%in", "type": "Accumulator" }"#, false, "");
    let err = expect_check_err(&input, preimage(0));
    assert!(err.contains("never verified"), "got: {err}");

    // `copy` cannot alias an accumulator: the alias could shadow another
    // pending one and drop its proof.
    let copied = r#"{ "op": "private_input", "guard": "0x00", "type": "Accumulator", "output": "%c" },
        { "op": "copy", "val": "%c", "output": "%d" },
        { "op": "verify_accumulator", "input": "%c" }"#;
    let err = expect_check_err(&ir(copied), preimage(0));
    assert!(
        err.contains("`copy` cannot take an accumulator"),
        "got: {err}"
    );
}

/// The accumulator instructions round-trip through JSON and binary.
#[test]
fn accumulator_text_format_roundtrips() {
    let ir = ir(&format!(
        "{},\n{}",
        bind_and_prepare(&[stub_ref(&VK_BLOB_A)]),
        r#"{ "op": "private_input", "guard": "0x01", "type": "Accumulator", "output": "%c" },
           { "op": "accumulate", "inputs": ["%a_0", "%c"], "output": "%a" },
           { "op": "verify_accumulator", "input": "%a" }"#,
    ));
    let json = serde_json::to_string(&ir).expect("serializes");
    assert_eq!(serde_json::from_str::<IrSource>(&json).expect("parses"), ir);

    let mut bytes = Vec::new();
    tagged_serialize(&ir, &mut bytes).expect("serializes");
    assert_eq!(
        tagged_deserialize::<IrSource>(&bytes[..]).expect("parses"),
        ir
    );
}

/// A `vk_id` with no matching key in the side-table is rejected, even when
/// the side-table has the right number of entries.
#[test]
fn vk_id_mismatch_is_rejected() {
    let blob = scalar_vk_blob(REAL_K);
    let other = scalar_vk_blob(REAL_K + 1);
    let correct = vk_ref(&blob);

    // Wrong key.
    let ir = ir_with_vks(&bind_and_verify_one(&correct), vec![other.clone()]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(err.contains("no verifying key"), "got: {err}");

    // Wrong `vk_id`.
    let ir = ir_with_vks(&bind_and_verify_one(&vk_ref(&other)), vec![blob.clone()]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(err.contains("no verifying key"), "got: {err}");

    // Matching pair: resolution succeeds, and the dummy proof then fails.
    let ir = ir_with_vks(&bind_and_verify_one(&correct), vec![blob]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(!err.contains("no verifying key"), "got: {err}");
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// Names a stub blob by a stand-in `vk_id`. Stubs are never resolved: their
/// `vk_id` cannot be computed, as they are not keys.
fn stub_ref(blob: &[u8]) -> String {
    stub_vk_ref(u64::from(blob[0]))
}

/// One `inner_proof` / `prepare_verification` pair under `guard`.
fn guarded_pair(i: usize, guard: &str, blob: &[u8]) -> String {
    format!(
        r#"{load},
           {{ "op": "inner_proof", "guard": "{guard}", "output": "%p_{i}" }},
           {{
               "op": "prepare_verification",
               "guard": "{guard}",
               "vk": "%k_{i}",
               "instance": ["0x7b"],
               "proof": "%p_{i}",
               "output": "%a_{i}"
           }},
           {{ "op": "verify_accumulator", "input": "%a_{i}" }}"#,
        load = load_vk(&format!("%k_{i}"), &stub_ref(blob)),
    )
}

fn count(instructions: &str) -> usize {
    ir(instructions).accumulator_count()
}

fn write(ir: &IrSource) -> Result<Vec<u8>, std::io::Error> {
    let mut bytes = Vec::new();
    Serializable::serialize(ir, &mut bytes)?;
    assert_eq!(
        bytes.len(),
        ir.serialized_size(),
        "serialized_size must agree with what serialize wrote"
    );
    Ok(bytes)
}

fn read(bytes: &[u8]) -> IrSource {
    Deserializable::deserialize(&mut { bytes }, 0).expect("deserialize IrSource")
}

fn instructions() -> String {
    bind_and_verify(&[stub_ref(&VK_BLOB_A), stub_ref(&VK_BLOB_B)])
}

/// The canonical IR with a side-table written inline. `Vec<Vec<u8>>` is an
/// array of byte arrays in JSON. The blobs are arbitrary here: nothing about
/// them is checked until the VM resolves them by hash.
fn ir_with_side_table() -> String {
    VERIFY_PROOF_IR.replace(
        "\"do_communications_commitment\": false,",
        "\"do_communications_commitment\": false,\n   \"inner_vks\": [[0, 1, 2]],",
    )
}

/// Parses `instructions` as a circuit with no inputs.
fn ir(instructions: &str) -> IrSource {
    load_ir("", false, instructions)
}

/// As [`ir`], with a side-table attached.
fn ir_with_vks(instructions: &str, vks: Vec<Vec<u8>>) -> IrSource {
    with_vks(ir(instructions), vks)
}

/// Binds `%p_0..%p_n`, then one `prepare_verification` per hash, into `%a_0..%a_n`.
/// Each gets a distinct instance so a round-trip that mixed them up would show.
fn bind_and_prepare(vks: &[String]) -> String {
    let loads = vks
        .iter()
        .enumerate()
        .map(|(i, h)| load_vk(&format!("%k_{i}"), h));
    let binds = (0..vks.len())
        .map(|i| format!(r#"{{ "op": "inner_proof", "guard": "0x01", "output": "%p_{i}" }}"#))
        .collect::<Vec<_>>();
    let verifies = vks.iter().enumerate().map(|(i, _)| {
        let instance = 0x7b + i;
        format!(
            r#"{{ "op": "prepare_verification", "guard": "0x01", "vk": "%k_{i}", "instance": ["0x{instance:02x}"], "proof": "%p_{i}", "output": "%a_{i}" }}"#
        )
    });
    loads
        .chain(binds)
        .chain(verifies)
        .collect::<Vec<_>>()
        .join(",\n")
}

/// [`bind_and_prepare`], verifying each accumulator.
fn bind_and_verify(vks: &[String]) -> String {
    let verifies =
        (0..vks.len()).map(|i| format!(r#"{{ "op": "verify_accumulator", "input": "%a_{i}" }}"#));
    std::iter::once(bind_and_prepare(vks))
        .chain(verifies)
        .collect::<Vec<_>>()
        .join(",\n")
}

/// [`bind_and_verify`] guarded off, so stub keys are never parsed.
fn bind_and_verify_off(vks: &[String]) -> String {
    bind_and_verify(vks).replace(r#""guard": "0x01""#, r#""guard": "0x00""#)
}

/// [`bind_and_verify`] for one hash.
fn bind_and_verify_one(vk: &str) -> String {
    bind_and_verify(&[vk.to_string()])
}

/// A preimage with `n` dummy proof witnesses.
fn preimage(n: usize) -> ProofPreimage {
    preimage_with(
        (0..n)
            .map(|i| InnerProofWitness::Direct(vec![i as u8; 8]))
            .collect(),
    )
}

/// Runs `check` and returns its error message.
fn expect_check_err(ir: &IrSource, preimage: ProofPreimage) -> String {
    match ir.check(&preimage) {
        Ok(_) => panic!("check unexpectedly succeeded"),
        Err(e) => format!("{e:#}"),
    }
}
