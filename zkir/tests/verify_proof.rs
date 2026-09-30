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

//! Tests for the `inner_proof` / `verify_proof` instruction pair that build no
//! outer circuit: the text format, IR serialization, and the checks `check`
//! runs on the IR and its proof witnesses. End-to-end tests are in
//! `verify_proof_e2e.rs`.

#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use midnight_zkir::IrSource;
use midnight_zkir::ir::IrMinorVersion;
use midnight_zkir::ir_instructions::verify_proof::verify_proof_offcircuit;
use serialize::{Deserializable, Serializable, tagged_deserialize, tagged_serialize};
use sha2::Digest;
use transient_crypto::proofs::{InnerProofWitness, ProofPreimage, Zkir};

use crate::verify_proof_common::{
    load_ir, preimage_with, scalar_inner_proof, test_rng, vk_hash_hex, with_vks,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Canonical, hash-only IR: `%p_0` is bound to the inner proof, the inner
/// statement is the single public input `%v_0`, and the instruction stores just
/// the VK hash. Neither the full VK nor the proof appears in the text — both
/// are supplied out-of-band.
///
/// The second `verify_proof` shows the other shape of the same operator: a
/// constant guard, always `0x01`, i.e. verify unconditionally.
const VERIFY_PROOF_IR: &str = r#"{
   "version": { "major": 3, "minor": 0 },
   "inputs": [
      { "name": "%v_0", "type": "Scalar<BLS12-381>" },
      { "name": "%g", "type": "Scalar<BLS12-381>" }
   ],
   "outputs": [],
   "do_communications_commitment": false,
   "instructions": [
       {
           "op": "inner_proof",
           "guard": "%g",
           "output": "%p_0"
       },
       {
           "op": "verify_proof",
           "guard": "%g",
           "vk_hash": "0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
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
           "op": "verify_proof",
           "guard": "0x01",
           "vk_hash": "0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff",
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

/// A lone `inner_proof` binding.
const BIND_ONE: &str = r#"{ "op": "inner_proof", "guard": "0x01", "output": "%p_0" }"#;

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// `accumulator_count()` is one per `verify_accumulator` instruction, whatever
/// the key or guard of the `verify_proof` it verifies.
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

    assert_eq!(count(&bind_and_verify_one(&vk_hash_hex(&VK_BLOB_A))), 1);
    assert_eq!(
        count(&bind_and_verify(&[
            vk_hash_hex(&VK_BLOB_A),
            vk_hash_hex(&VK_BLOB_B)
        ])),
        2
    );

    // Two instructions sharing one key still expose two accumulators.
    assert_eq!(
        count(&bind_and_verify(&[
            vk_hash_hex(&VK_BLOB_A),
            vk_hash_hex(&VK_BLOB_A)
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
    // guarded-off `verify_proof` still counts.
    for guard in ["0x01", "0x00", "%v_0"] {
        assert_eq!(
            count(&guarded_pair(0, guard, &VK_BLOB_A)),
            1,
            "guard {guard}: a guarded-off verify_proof still exposes the trivial accumulator"
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

    let aggregated = format!(
        "{},\n{}",
        bind_and_prepare(&[vk_hash_hex(&VK_BLOB_A), vk_hash_hex(&VK_BLOB_B)]),
        r#"{ "op": "aggregate_accumulators", "inputs": ["%a_0", "%a_1"], "output": "%a" },
           { "op": "verify_accumulator", "input": "%a" }"#,
    );
    assert_eq!(
        count(&aggregated),
        1,
        "aggregated accumulators are exposed once"
    );

    let ir_hash_only: IrSource = ir(&bind_and_verify_one(&vk_hash_hex(&VK_BLOB_A)));
    let mut ir_with_keys = ir_hash_only.clone();
    ir_with_keys.verify_proof_vks = vec![VK_BLOB_A.to_vec()];
    assert_eq!(
        ir_hash_only.accumulator_count(),
        ir_with_keys.accumulator_count(),
        "resolving the side-table must not change the exposed shape"
    );
}

/// The same VK blob listed twice in `verify_proof_vks` is rejected, even though
/// an instruction uses it. The side-table is indexed by digest, so the second
/// copy could never be resolved.
#[test]
fn duplicate_vk_in_side_table_is_rejected() {
    let duplicated = ir_with_vks(
        &bind_and_verify_one(&vk_hash_hex(&VK_BLOB_A)),
        vec![VK_BLOB_A.to_vec(), VK_BLOB_A.to_vec()],
    );
    let err = expect_check_err(&duplicated, preimage(1));
    assert!(err.contains("duplicate verifying key"), "got: {err}");
}

/// Only a `V1` IR carries `verify_proof_vks` in its binary form, and writing a
/// `V0` that has one fails.
#[test]
fn ir_minor_version_gates_the_vk_side_table() {
    let v0 = ir(BIND_ONE);
    assert_eq!(v0.version, IrMinorVersion::V0, "text IR parses as V0");
    assert!(v0.verify_proof_vks.is_empty());

    let back = read(&write(&v0).expect("a V0 with no side-table must write"));
    assert_eq!(back, v0, "a V0 must round-trip");
    assert!(back.verify_proof_vks.is_empty());

    let v1 = ir_with_vks(BIND_ONE, vec![VK_BLOB_A.to_vec()]);
    assert_eq!(v1.version, IrMinorVersion::V1);

    let bytes = write(&v1).expect("a V1 with a side-table must write");
    let back = read(&bytes);
    assert_eq!(back, v1, "a V1 must round-trip");
    assert_eq!(
        back.verify_proof_vks,
        vec![VK_BLOB_A.to_vec()],
        "the side-table must survive"
    );

    // A V0 with a side-table has no encoding.
    let mut inconsistent = ir(BIND_ONE);
    inconsistent.verify_proof_vks = vec![VK_BLOB_A.to_vec()];
    assert_eq!(inconsistent.version, IrMinorVersion::V0);

    let err = write(&inconsistent)
        .expect_err("a V0 carrying a side-table has no encoding and must not be written");
    assert!(
        format!("{err}").contains("V1"),
        "the error should name the version required: {err}"
    );
}

/// `vk_hash` and `verify_proof_vks` survive JSON and binary round-trips, in
/// order.
#[test]
fn ir_round_trip_preserves_vks_in_order() {
    let ir = ir_with_vks(
        &instructions(),
        vec![VK_BLOB_A.to_vec(), VK_BLOB_B.to_vec()],
    );

    let json = serde_json::to_string(&ir).expect("serializes");
    assert!(json.contains("verify_proof_vks"), "{json}");
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
        &bind_and_verify_one(&vk_hash_hex(&inner.vk_blob)),
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

    let from_real = verify_proof_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
        .expect("preparation of the real proof");
    let from_padded = verify_proof_offcircuit(&inner.vk_blob, &inner.pis, &padded, true)
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

    let err = expect_check_err(&ir_with_vks("", vec![VK_BLOB_A.to_vec()]), preimage(0));
    assert!(
        err.contains("verify_proof_vks") && err.contains("used"),
        "got: {err}"
    );

    // Guarded off, so the stub key is never parsed.
    let paired = ir_with_vks(
        &bind_and_verify_off(&[vk_hash_hex(&VK_BLOB_A)]),
        vec![VK_BLOB_A.to_vec()],
    );
    let err = expect_check_err(&paired, preimage(2));
    assert!(err.contains("proof witnesses"), "got: {err}");

    ir("").check(&preimage(0)).expect("empty circuit");
    paired
        .check(&preimage(1))
        .expect("one binding, one witness");
}

/// The `inner_proof` / `verify_proof` text format round-trips through JSON.
///
/// `inner_proof` binds the next inner proof witness to a name, which
/// `verify_proof` takes as its `proof` input. `vk_hash` names a key in the
/// `verify_proof_vks` side-table; the text stores only the hash. Guards are
/// ordinary operands, a variable or a `0x` immediate. The `vk_hash` here is
/// fake: nothing is verified.
#[test]
fn verify_proof_text_format_roundtrips() {
    let ir = IrSource::load(VERIFY_PROOF_IR.as_bytes()).expect("verify_proof IR must parse");

    // A hash-only IR carries no VK bytes.
    assert!(
        ir.verify_proof_vks.is_empty(),
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
    assert!(json.contains("verify_proof"), "op tag missing:\n{json}");
    assert!(json.contains("%p_0"), "proof operand missing:\n{json}");
    assert!(
        json.contains("0x00112233445566778899aabbccddeeff00112233445566778899aabbccddeeff"),
        "vk_hash hex missing:\n{json}"
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
        !json.contains("verify_proof_vks"),
        "empty VK side-table should be omitted:\n{json}"
    );
}

/// A side-table exists only from `V1` on, so text carrying one must declare
/// `minor: 1`. The inconsistent document is refused at load.
#[test]
fn side_table_requires_minor_1() {
    let ir = IrSource::load(ir_with_side_table(1).as_bytes()).expect("`minor: 1` must load");
    assert_eq!(ir.version, IrMinorVersion::V1);
    assert_eq!(ir.verify_proof_vks, vec![vec![0u8, 1, 2]]);
    tagged_serialize(&ir, &mut Vec::new()).expect("a V1 carrying a side-table must serialize");

    assert!(
        IrSource::load(ir_with_side_table(0).as_bytes()).is_err(),
        "`minor: 0` must not accept a side-table"
    );
}

/// Every accumulator must reach exactly one `aggregate_accumulators` or
/// `verify_accumulator`: a dropped one is an unchecked proof.
#[test]
fn every_accumulator_is_verified_exactly_once() {
    let prepared = bind_and_prepare(&[vk_hash_hex(&VK_BLOB_A)]);
    let err = expect_check_err(&ir(&prepared), preimage(1));
    assert!(err.contains("never verified"), "got: {err}");

    let verify_one = bind_and_verify_one(&vk_hash_hex(&VK_BLOB_A));
    let twice = format!(r#"{verify_one},{{ "op": "verify_accumulator", "input": "%a_0" }}"#);
    let err = expect_check_err(&ir(&twice), preimage(1));
    assert!(err.contains("not an unconsumed accumulator"), "got: {err}");

    let witnessed =
        r#"{ "op": "private_input", "guard": "0x00", "type": "Accumulator", "output": "%c" }"#;
    let err = expect_check_err(&ir(witnessed), preimage(0));
    assert!(err.contains("never verified"), "got: {err}");

    // Neither `%x` nor `%y` was produced, so `%x` cannot feed itself.
    let self_fed = r#"{ "op": "aggregate_accumulators", "inputs": ["%x", "%y"], "output": "%x" }"#;
    let err = expect_check_err(&ir(self_fed), preimage(0));
    assert!(err.contains("not an unconsumed accumulator"), "got: {err}");
}

/// The accumulator instructions round-trip through JSON and binary.
#[test]
fn accumulator_text_format_roundtrips() {
    let ir = ir(&format!(
        "{},\n{}",
        bind_and_prepare(&[vk_hash_hex(&VK_BLOB_A)]),
        r#"{ "op": "private_input", "guard": "0x01", "type": "Accumulator", "output": "%c" },
           { "op": "aggregate_accumulators", "inputs": ["%a_0", "%c"], "output": "%a" },
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

/// A `vk_hash` with no matching blob in the side-table is rejected, even when
/// the side-table has the right number of entries.
#[test]
fn vk_hash_mismatch_is_rejected() {
    let correct = vk_hash_hex(&VK_BLOB_A);

    // Wrong blob.
    let ir = ir_with_vks(&bind_and_verify_one(&correct), vec![VK_BLOB_B.to_vec()]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(
        err.contains("no verifying key") && err.contains(&correct),
        "got: {err}"
    );

    // Wrong digest.
    let mut altered = sha2::Sha256::digest(VK_BLOB_A).to_vec();
    altered[0] ^= 0x01;
    let altered = const_hex::encode(&altered);
    let ir = ir_with_vks(&bind_and_verify_one(&altered), vec![VK_BLOB_A.to_vec()]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(
        err.contains("no verifying key") && err.contains(&altered),
        "got: {err}"
    );

    // Matching pair: resolution succeeds, and the stub key then fails to parse.
    let ir = ir_with_vks(&bind_and_verify_one(&correct), vec![VK_BLOB_A.to_vec()]);
    let err = expect_check_err(&ir, preimage(1));
    assert!(
        err.contains("verifying key") && !err.contains("no verifying key"),
        "got: {err}"
    );
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// One `inner_proof` / `verify_proof` pair under `guard`.
fn guarded_pair(i: usize, guard: &str, blob: &[u8]) -> String {
    format!(
        r#"{{ "op": "inner_proof", "guard": "{guard}", "output": "%p_{i}" }},
           {{
               "op": "verify_proof",
               "guard": "{guard}",
               "vk_hash": "0x{hash}",
               "instance": ["0x7b"],
               "proof": "%p_{i}",
               "output": "%a_{i}"
           }},
           {{ "op": "verify_accumulator", "input": "%a_{i}" }}"#,
        hash = vk_hash_hex(blob),
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
    bind_and_verify(&[vk_hash_hex(&VK_BLOB_A), vk_hash_hex(&VK_BLOB_B)])
}

/// The canonical IR with a side-table written inline, declaring `minor`.
/// `Vec<Vec<u8>>` is an array of byte arrays in JSON. The blobs are arbitrary
/// here: nothing about them is checked until the VM resolves them by hash.
fn ir_with_side_table(minor: u8) -> String {
    VERIFY_PROOF_IR
        .replace("\"minor\": 0", &format!("\"minor\": {minor}"))
        .replace(
            "\"do_communications_commitment\": false,",
            "\"do_communications_commitment\": false,\n   \"verify_proof_vks\": [[0, 1, 2]],",
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

/// Binds `%p_0..%p_n`, then one `verify_proof` per hash, into `%a_0..%a_n`.
/// Each gets a distinct instance so a round-trip that mixed them up would show.
fn bind_and_prepare(vk_hashes: &[String]) -> String {
    let binds = (0..vk_hashes.len())
        .map(|i| format!(r#"{{ "op": "inner_proof", "guard": "0x01", "output": "%p_{i}" }}"#))
        .collect::<Vec<_>>();
    let verifies = vk_hashes.iter().enumerate().map(|(i, h)| {
        let instance = 0x7b + i;
        format!(
            r#"{{ "op": "verify_proof", "guard": "0x01", "vk_hash": "0x{h}", "instance": ["0x{instance:02x}"], "proof": "%p_{i}", "output": "%a_{i}" }}"#
        )
    });
    binds
        .into_iter()
        .chain(verifies)
        .collect::<Vec<_>>()
        .join(",\n")
}

/// [`bind_and_prepare`], verifying each accumulator.
fn bind_and_verify(vk_hashes: &[String]) -> String {
    let verifies = (0..vk_hashes.len())
        .map(|i| format!(r#"{{ "op": "verify_accumulator", "input": "%a_{i}" }}"#));
    std::iter::once(bind_and_prepare(vk_hashes))
        .chain(verifies)
        .collect::<Vec<_>>()
        .join(",\n")
}

/// [`bind_and_verify`] guarded off, so stub keys are never parsed.
fn bind_and_verify_off(vk_hashes: &[String]) -> String {
    bind_and_verify(vk_hashes).replace(r#""guard": "0x01""#, r#""guard": "0x00""#)
}

/// [`bind_and_verify`] for one hash.
fn bind_and_verify_one(vk_hash: &str) -> String {
    bind_and_verify(&[vk_hash.to_string()])
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
