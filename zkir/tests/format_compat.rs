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

//! Serialization-format compatibility guards.
//!
//! The fixtures under `tests/compat_fixtures/` pin both the JSON and the
//! binary form of `IrSource` documents exercising every `Instruction`
//! variant and every `IrType`. The binary encoding of derived enums is a
//! positional `u8` discriminant, so removing, inserting (anywhere but the
//! end), or reordering variants silently changes the wire format — and the
//! `tag_enforcement_test!` fingerprint cannot see a swap of two variants
//! with identical field types (e.g. `Add`/`Mul`). These tests turn all of
//! that into hard failures:
//!
//! - the `.zkir` fixture must keep loading: `op` names, `IrType` names, and
//!   mandatory fields are part of the JSON format, so renaming or removing
//!   an operation, or adding a non-optional field to one, fails here;
//! - its binary serialization must stay byte-identical to the committed
//!   `.bzkir` golden, and the golden must deserialize back to the same IR.
//!
//! In CI these fixtures are additionally taken from the PR's *target branch*
//! (via `ZKIR_COMPAT_FIXTURES_DIR`), so a PR cannot dodge the check by
//! updating the fixtures and goldens in the same change.
//!
//! Refresh the goldens after an intentional format change — note that this
//! is a breaking change to the ZKIR wire format and needs a major version
//! bump:
//!
//! ```text
//! UPDATE_ZKIR_GOLDEN=1 cargo test -p midnight-zkir --test format_compat
//! ```

use midnight_zkir::IrSource;
use serialize::{tagged_deserialize, tagged_serialize};
use std::ffi::OsStr;
use std::fs::{self, File};
use std::io::{BufReader, Cursor};
use std::path::{Path, PathBuf};

const UPDATE_ENV: &str = "UPDATE_ZKIR_GOLDEN";
const CORPUS_ENV: &str = "ZKIR_COMPAT_FIXTURES_DIR";
const REFRESH_HINT: &str = "Run `UPDATE_ZKIR_GOLDEN=1 cargo test -p midnight-zkir --test format_compat` to refresh — but note this changes the ZKIR wire format, which is a breaking change requiring a major version bump.";

fn fixtures_dir() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests")
        .join("compat_fixtures")
}

fn enumerate_by_extension(root: &Path, ext: &str) -> Vec<PathBuf> {
    let mut out = Vec::new();
    let mut stack = vec![root.to_path_buf()];
    while let Some(dir) = stack.pop() {
        let entries = fs::read_dir(&dir).unwrap_or_else(|e| panic!("read_dir {dir:?}: {e}"));
        for entry in entries {
            let path = entry.expect("dir entry").path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension() == Some(OsStr::new(ext)) {
                out.push(path);
            }
        }
    }
    out.sort();
    out
}

/// The declared `version.major` of a `.zkir` JSON document, without
/// interpreting anything else. The compat corpus can contain documents of
/// other majors (e.g. `zkir-precompiles` holds `major: 2` files predating
/// this crate); those are not this crate's to validate.
fn json_major(path: &Path) -> u8 {
    let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
    let doc: serde_json::Value = serde_json::from_reader(BufReader::new(file))
        .unwrap_or_else(|e| panic!("{path:?} is not valid JSON: {e}"));
    doc["version"]["major"]
        .as_u64()
        .unwrap_or_else(|| panic!("{path:?} has no numeric version.major")) as u8
}

fn load(path: &Path) -> IrSource {
    let file = File::open(path).unwrap_or_else(|e| panic!("open {path:?}: {e}"));
    IrSource::load(BufReader::new(file))
        .unwrap_or_else(|e| panic!("v3 IR {path:?} no longer loads: {e}"))
}

/// Every committed `.zkir` fixture keeps loading, its binary serialization is
/// byte-identical to the committed `.bzkir` golden, and the golden
/// deserializes back to the same `IrSource`.
#[test]
fn golden_fixtures_pinned() {
    let update = std::env::var_os(UPDATE_ENV).is_some();
    // Top-level fixtures only: subdirectories hold frozen release baselines
    // (e.g. `v3.0/`), produced by the release binary and never refreshed.
    let files: Vec<_> = enumerate_by_extension(&fixtures_dir(), "zkir")
        .into_iter()
        .filter(|p| p.parent() == Some(fixtures_dir().as_path()))
        .collect();
    assert!(!files.is_empty(), "no .zkir fixtures found");

    for zkir_path in &files {
        let ir = load(zkir_path);
        let mut bytes = Vec::new();
        tagged_serialize(&ir, &mut bytes).unwrap_or_else(|e| panic!("serialize {zkir_path:?}: {e}"));

        let golden_path = zkir_path.with_extension("bzkir");
        if update {
            fs::write(&golden_path, &bytes)
                .unwrap_or_else(|e| panic!("write {golden_path:?}: {e}"));
            eprintln!("refreshed {golden_path:?} ({} bytes)", bytes.len());
            continue;
        }

        let golden = fs::read(&golden_path).unwrap_or_else(|e| {
            panic!("missing golden {golden_path:?}: {e}\n{REFRESH_HINT}")
        });
        if bytes != golden {
            let diff_at = bytes
                .iter()
                .zip(golden.iter())
                .position(|(a, b)| a != b)
                .unwrap_or_else(|| bytes.len().min(golden.len()));
            panic!(
                "binary encoding of {zkir_path:?} drifted from {golden_path:?}: \
                 first difference at byte {diff_at} (produced {} bytes, golden {} bytes).\n\
                 This means the ZKIR binary format changed.\n{REFRESH_HINT}",
                bytes.len(),
                golden.len(),
            );
        }

        let round: IrSource = tagged_deserialize(Cursor::new(&golden))
            .unwrap_or_else(|e| panic!("golden {golden_path:?} no longer deserializes: {e}"));
        assert_eq!(
            round, ir,
            "golden {golden_path:?} deserializes to a different IR than {zkir_path:?}"
        );
    }
}

/// Backwards compatibility against an externally supplied corpus.
///
/// With `ZKIR_COMPAT_FIXTURES_DIR` unset this re-checks the in-repo fixtures
/// (subsumed by `golden_fixtures_pinned`). In CI it points at a checkout of
/// the PR's target branch, so every `major: 3` `.zkir` and every `.bzkir`
/// that the *old* code produced must still be readable by *this* code, and
/// where both representations of the same circuit exist they must agree.
#[test]
fn corpus_stays_readable() {
    let root = std::env::var_os(CORPUS_ENV)
        .map(PathBuf::from)
        .unwrap_or_else(fixtures_dir);
    assert!(root.is_dir(), "compat corpus {root:?} is not a directory");

    let mut checked = 0usize;

    for zkir_path in enumerate_by_extension(&root, "zkir") {
        if json_major(&zkir_path) != 3 {
            continue;
        }
        load(&zkir_path);
        checked += 1;
    }

    for bzkir_path in enumerate_by_extension(&root, "bzkir") {
        let bytes =
            fs::read(&bzkir_path).unwrap_or_else(|e| panic!("read {bzkir_path:?}: {e}"));
        let ir: IrSource = tagged_deserialize(Cursor::new(&bytes)).unwrap_or_else(|e| {
            panic!("binary IR {bzkir_path:?} no longer deserializes: {e}")
        });
        // Decoding alone is not enough: a misaligned layout can decode into a
        // different, valid IR. Require a JSON twin and an exact round trip.
        let zkir_path = bzkir_path.with_extension("zkir");
        assert!(
            zkir_path.is_file() && json_major(&zkir_path) == 3,
            "{bzkir_path:?} has no v3 JSON twin {zkir_path:?}"
        );
        assert_eq!(
            ir,
            load(&zkir_path),
            "{bzkir_path:?} and {zkir_path:?} decode to different IRs"
        );
        let mut round = Vec::new();
        tagged_serialize(&ir, &mut round)
            .unwrap_or_else(|e| panic!("serialize {bzkir_path:?}: {e}"));
        assert!(
            round == bytes,
            "{bzkir_path:?} does not round-trip byte-exactly"
        );
        checked += 1;
    }

    assert!(checked > 0, "compat corpus {root:?} contained no v3 files");
    eprintln!("checked {checked} corpus files under {root:?}");
}
