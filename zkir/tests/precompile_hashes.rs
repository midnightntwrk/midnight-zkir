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

//! Regression tests pinning prover/verifier key SHA-256 hashes for the
//! `major: 3` precompiles under `zkir-precompiles/`.
//!
//! Deployed verifiers hold the exact key bytes these pins record. Without
//! them, a change in `zkir`, `midnight-zk-stdlib`, `midnight-proofs`,
//! `midnight-circuits`, or `serialize` could silently shift the distributed
//! keys and break on-chain verification. In CI the precompiles (and their
//! pins) are additionally taken from the PR's target branch via
//! `ZKIR_PRECOMPILES_DIR`, making "same file, same verifier key" a hard
//! cross-branch requirement.
//!
//! Refresh after an intentional key change:
//!
//! ```text
//! UPDATE_ZKIR_HASHES=1 cargo test -p midnight-zkir --release --test precompile_hashes
//! ```

mod common;

use common::TestParams;
use midnight_zkir::IrSource;
use serialize::tagged_serialize;
use sha2::{Digest, Sha256};
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{BufReader, Write};
use std::path::{Path, PathBuf};
use transient_crypto::proofs::Zkir;

const UPDATE_ENV: &str = "UPDATE_ZKIR_HASHES";
const ROOT_ENV: &str = "ZKIR_PRECOMPILES_DIR";
const REFRESH_HINT: &str = "Run `UPDATE_ZKIR_HASHES=1 cargo test -p midnight-zkir --release --test precompile_hashes` to refresh.";

fn precompiles_root() -> PathBuf {
    std::env::var_os(ROOT_ENV).map(PathBuf::from).unwrap_or_else(|| {
        Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("..")
            .join("zkir-precompiles")
    })
}

fn enumerate_zkir(root: &Path) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension() == Some(OsStr::new("zkir")) {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

fn json_major(path: &Path) -> u8 {
    let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
    let doc: serde_json::Value = serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|e| panic!("{path:?} is not valid JSON: {e}"));
    doc["version"]["major"]
        .as_u64()
        .unwrap_or_else(|| panic!("{path:?} has no numeric version.major")) as u8
}

fn hex_digest(bytes: &[u8]) -> String {
    let mut h = Sha256::new();
    h.update(bytes);
    hex::encode(h.finalize())
}

/// Write `<hex> <artifact_label>` to the pin file, in `sha256sum` format.
fn write_pin_file(pin_path: &Path, artifact_label: &str, bytes: &[u8]) {
    let mut f = File::create(pin_path).unwrap_or_else(|e| panic!("create {pin_path:?}: {e}"));
    writeln!(f, "{}  {}", hex_digest(bytes), artifact_label)
        .unwrap_or_else(|e| panic!("write {pin_path:?}: {e}"));
}

fn read_pinned_hex(pin_path: &Path) -> std::io::Result<String> {
    let contents = fs::read_to_string(pin_path)?;
    Ok(contents.split_whitespace().next().unwrap_or("").to_string())
}

#[actix_rt::test]
async fn precompile_key_hashes_pinned() {
    check_key_pins(&precompiles_root(), std::env::var_os(UPDATE_ENV).is_some()).await;
}

/// The frozen ZKIR 3.0 baseline: files, `.bzkir`s and a `keys.sha256`
/// manifest produced by the 3.0.0-rc.2 release binary, covering every 3.0
/// instruction and type. Old files must keygen to the exact keys the release
/// produced. These pins are never refreshed.
#[actix_rt::test]
async fn frozen_v3_0_key_hashes_pinned() {
    let root = Path::new(env!("CARGO_MANIFEST_DIR")).join("tests/compat_fixtures/v3.0");
    check_key_pins(&root, false).await;
}

async fn check_key_pins(root: &Path, update: bool) {
    let files = enumerate_zkir(root);
    assert!(!files.is_empty(), "no .zkir files found under {root:?}");

    // A directory may pin all its keys in one `keys.sha256` manifest
    // (`sha256sum` format) instead of per-file `.sha256` pins.
    let manifest = fs::read_to_string(root.join("keys.sha256")).ok();

    let mut mismatches: Vec<String> = Vec::new();
    let mut checked = 0usize;

    for zkir_path in &files {
        // `major: 2` precompiles predate this crate and cannot be loaded by
        // it; a `major: 3` file failing to load is a hard error here.
        if json_major(zkir_path) != 3 {
            continue;
        }
        let ir = IrSource::load(BufReader::new(
            File::open(zkir_path).unwrap_or_else(|e| panic!("open {zkir_path:?}: {e}")),
        ))
        .unwrap_or_else(|e| panic!("v3 IR {zkir_path:?} no longer loads: {e}"));
        checked += 1;

        let (pk, vk) = ir.keygen(&TestParams).await.expect("keygen must succeed");
        let mut pk_bytes = Vec::new();
        tagged_serialize(&pk, &mut pk_bytes).expect("serialize prover key");
        let mut vk_bytes = Vec::new();
        tagged_serialize(&vk, &mut vk_bytes).expect("serialize verifier key");

        let stem = zkir_path
            .file_stem()
            .expect("stem")
            .to_string_lossy()
            .into_owned();
        let pk_label = format!("{stem}.prover");
        let vk_label = format!("{stem}.verifier");
        let pk_pin = zkir_path.with_extension("prover.sha256");
        let vk_pin = zkir_path.with_extension("verifier.sha256");

        if update {
            write_pin_file(&pk_pin, &pk_label, &pk_bytes);
            write_pin_file(&vk_pin, &vk_label, &vk_bytes);
            continue;
        }

        for (label, bytes, pin_path) in [
            (&pk_label, &pk_bytes, &pk_pin),
            (&vk_label, &vk_bytes, &vk_pin),
        ] {
            let actual = hex_digest(bytes);
            let pinned = match &manifest {
                Some(m) => m
                    .lines()
                    .find_map(|l| {
                        let mut it = l.split_whitespace();
                        let hash = it.next()?;
                        (it.next()? == label.as_str()).then(|| hash.to_string())
                    })
                    .ok_or_else(|| std::io::Error::other("not listed in keys.sha256")),
                None => read_pinned_hex(pin_path),
            };
            let expected = match pinned {
                Ok(s) => s,
                Err(e) => {
                    mismatches.push(format!(
                        "{label}: missing pinned hash file {pin_path:?} ({e})"
                    ));
                    continue;
                }
            };
            if actual != expected {
                mismatches.push(format!(
                    "{label}: hash drift\n    expected: {expected}\n    actual:   {actual}\n    pin file: {pin_path:?}"
                ));
            }
        }
    }

    assert!(checked > 0, "no major: 3 precompiles found under {root:?}");

    if update {
        eprintln!("Refreshed {checked} v3 prover+verifier hash pin files under {root:?}.");
        return;
    }

    assert!(
        mismatches.is_empty(),
        "{} key hash mismatch(es):\n\n{}\n\n{REFRESH_HINT}",
        mismatches.len(),
        mismatches.join("\n\n"),
    );
}
