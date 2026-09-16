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

//! `verify_inner_proof` against the real artifacts in `tests/assets/`.
//!
//! `external_artifacts.md` describes where those come from and what a full
//! end-to-end run proves. This is the cheap half of it: no proving and no outer
//! circuit, just the off-circuit verification of two inner proofs that are
//! already checked in. They were made against the Midnight SRS, which is the
//! one `verify_inner_proof` pairs against, so they are the only proofs in this
//! repository it can accept -- `verify_proof_e2e.rs` generates its own setup.

use std::fs;
use std::path::PathBuf;

use group::ff::Field;
use midnight_zkir::ir_instructions::verify_proof::verify_inner_proof;
use transient_crypto::curve::{Fr, outer};

/// The runbook lets `$MIDNIGHT_ZK_ARTIFACTS` stand in for `tests/assets/`.
fn asset_dir(name: &str) -> PathBuf {
    let base = std::env::var("MIDNIGHT_ZK_ARTIFACTS")
        .unwrap_or_else(|_| format!("{}/tests/assets", env!("CARGO_MANIFEST_DIR")));
    PathBuf::from(base).join(name)
}

/// One `0x`-prefixed field element per line, minimal width, in the byte order
/// `Fr::from_le_bytes` reads -- the same one a `0x` immediate takes in the IR
/// text format.
fn read_instance(dir: &PathBuf) -> Vec<outer::Scalar> {
    fs::read_to_string(dir.join("instance.hex"))
        .expect("instance.hex")
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .map(|line| {
            let hex = line.strip_prefix("0x").expect("a `0x` prefix");
            let bytes = const_hex::decode(hex).expect("hex digits");
            Fr::from_le_bytes(&bytes).expect("in range for the field").0
        })
        .collect()
}

fn read_artifact(name: &str) -> (Vec<u8>, Vec<outer::Scalar>, Vec<u8>) {
    let dir = asset_dir(name);
    let vk = fs::read(dir.join("vk_ledger.bin")).expect("vk_ledger.bin");
    let proof = fs::read(dir.join("proof.bin")).expect("proof.bin");
    (vk, read_instance(&dir), proof)
}

/// `DeciderKind::None`: the accumulator the instruction exposes is the proof's
/// own, so the pairing here is the whole verdict.
#[test]
fn cred_ledger_artifact_verifies() {
    let (vk, instance, proof) = read_artifact("cred_ledger");

    verify_inner_proof(&vk, &instance, &proof).expect("the checked-in artifact verifies");

    // The instance is the statement, so changing a field asks for a proof of
    // something else. `plonk::prepare` returns `Ok` on that and only the
    // pairing rejects it, which is the whole reason the pairing is run.
    let mut wrong = instance.clone();
    wrong[0] += outer::Scalar::ONE;
    let rejected = verify_inner_proof(&vk, &wrong, &proof).expect_err("a proof of another statement");
    assert!(
        rejected.to_string().contains("does not hold"),
        "rejected by the pairing, not an earlier layer: {rejected}"
    );

    let mut corrupted = proof.clone();
    *corrupted.last_mut().expect("a non-empty proof") ^= 0xff;
    assert!(verify_inner_proof(&vk, &instance, &corrupted).is_err());
}

/// `DeciderKind::Collapsed`: the instruction folds in the accumulator the proof
/// carries in its instance tail, so one pairing discharges both.
#[test]
fn ivc_ledger_artifact_verifies() {
    let (vk, instance, proof) = read_artifact("ivc_ledger");

    verify_inner_proof(&vk, &instance, &proof).expect("the checked-in artifact verifies");

    // Only the head field, never the tail: a malformed carried accumulator is
    // rejected before the pairing, which would pass this for the wrong reason.
    let mut wrong = instance.clone();
    wrong[0] += outer::Scalar::ONE;
    let rejected = verify_inner_proof(&vk, &wrong, &proof).expect_err("a proof of another statement");
    assert!(
        rejected.to_string().contains("does not hold"),
        "rejected by the pairing, not an earlier layer: {rejected}"
    );
}
