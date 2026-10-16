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

//! The `sow-26q3` feature gates 2026-Q3 functionality: the Secp256r1 and
//! Curve25519 types and everything ZKIR 3.1 added (`Bool`, `Byte`,
//! `Bytes<n != 32>` and the instructions after the ZKIR 3.0 marker).
//!
//! Without the feature, such IR must be refused at every entry point; with it,
//! the same IR must load. Run the gated half with
//! `cargo nextest run -p midnight-zkir --no-default-features -E 'test(sow_26q3)'`.

use midnight_zkir::{Identifier, Instruction, IrSource};
use std::sync::Arc;

/// One IR per kind of 2026-Q3 usage, with the substring the refusal must name.
const Q3_IRS: &[(&str, &str)] = &[
    (
        r#"{
           "version": { "major": 3, "minor": 0 },
           "inputs": [ { "name": "%v_0", "type": "Point<Secp256r1>" } ],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": []
        }"#,
        "Secp256r1Point",
    ),
    (
        r#"{
           "version": { "major": 3, "minor": 0 },
           "inputs": [],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": [
               { "op": "private_input", "type": "Scalar<Curve25519>", "guard": null, "output": "%s" }
           ]
        }"#,
        "Curve25519Scalar",
    ),
    (
        r#"{
           "version": { "major": 3, "minor": 0 },
           "inputs": [],
           "outputs": ["Bool"],
           "do_communications_commitment": false,
           "instructions": []
        }"#,
        "Bool",
    ),
    (
        r#"{
           "version": { "major": 3, "minor": 0 },
           "inputs": [ { "name": "%v_0", "type": "Scalar<BLS12-381>" } ],
           "outputs": [],
           "do_communications_commitment": false,
           "instructions": [
               { "op": "sha512", "alignment": [ { "tag": "atom", "value": { "tag": "bytes", "length": 1 } } ], "inputs": ["%v_0"], "output": "%v_1" }
           ]
        }"#,
        "Sha512",
    ),
];

/// Q2 functionality only: secp256k1, Keccak, `Bytes<32>`.
const Q2_IR: &str = r#"{
   "version": { "major": 3, "minor": 0 },
   "inputs": [
      { "name": "%v_0", "type": "Scalar<BLS12-381>" },
      { "name": "%p", "type": "Point<Secp256k1>" }
   ],
   "outputs": [],
   "do_communications_commitment": false,
   "instructions": [
       { "op": "private_input", "type": "Bytes<32>", "guard": null, "output": "%b" },
       { "op": "keccak256", "alignment": [ { "tag": "atom", "value": { "tag": "bytes", "length": 1 } } ], "inputs": ["%v_0"], "output": "%v_1" }
   ]
}"#;

/// Built in code so it exists even when the JSON loader refuses it.
fn q3_ir_built_directly() -> IrSource {
    IrSource {
        version: Default::default(),
        inputs: vec![],
        outputs: vec![],
        do_communications_commitment: false,
        instructions: Arc::new(vec![Instruction::And {
            inputs: vec![],
            output: Identifier("%o".into()),
        }]),
    }
}

#[test]
fn sow_26q3_q2_ir_always_loads() {
    let ir = IrSource::load(Q2_IR.as_bytes()).expect("Q2 IR must load in every build");
    ir.check_feature_gates()
        .expect("Q2 IR must pass the feature gates in every build");
}

#[cfg(not(feature = "sow-26q3"))]
mod gated {
    use super::*;
    use std::borrow::Cow;
    use transient_crypto::proofs::{KeyLocation, ProofPreimage, Zkir};

    fn empty_preimage() -> ProofPreimage {
        ProofPreimage {
            binding_input: 0.into(),
            communications_commitment: None,
            inputs: vec![],
            private_transcript: vec![],
            public_transcript_inputs: vec![],
            public_transcript_outputs: vec![],
            key_location: KeyLocation(Cow::Borrowed("builtin")),
        }
    }

    fn assert_refused(err: impl std::fmt::Display, what: &str) {
        let msg = err.to_string();
        assert!(
            msg.contains("sow-26q3") && msg.contains(what),
            "refusal {msg:?} must name the `sow-26q3` feature and {what:?}"
        );
    }

    #[test]
    fn sow_26q3_json_load_refuses_q3_ir() {
        for (raw, what) in Q3_IRS {
            let err = IrSource::load(raw.as_bytes())
                .expect_err(&format!("IR using {what} must be refused"));
            assert_refused(err, what);
        }
    }

    #[test]
    fn sow_26q3_check_feature_gates_refuses_q3_ir() {
        assert_refused(
            q3_ir_built_directly().check_feature_gates().unwrap_err(),
            "And",
        );
    }

    #[test]
    fn sow_26q3_tagged_load_refuses_q3_ir() {
        let mut raw = Vec::new();
        serialize::tagged_serialize(&q3_ir_built_directly(), &mut raw).unwrap();
        let err = <IrSource as Zkir>::load_ir_from_tagged(std::io::Cursor::new(raw))
            .expect_err("tagged IR using `And` must be refused");
        assert_refused(err, "And");
    }

    #[test]
    fn sow_26q3_check_refuses_q3_ir() {
        let err = Zkir::check(&q3_ir_built_directly(), &empty_preimage())
            .expect_err("checking IR using `And` must be refused");
        assert_refused(err, "And");
    }
}

#[cfg(feature = "sow-26q3")]
#[test]
fn sow_26q3_enabled_loads_q3_ir() {
    for (raw, what) in Q3_IRS {
        let ir = IrSource::load(raw.as_bytes())
            .unwrap_or_else(|e| panic!("IR using {what} must load with `sow-26q3`: {e}"));
        ir.check_feature_gates()
            .unwrap_or_else(|e| panic!("IR using {what} must pass with `sow-26q3`: {e}"));
    }
    q3_ir_built_directly().check_feature_gates().unwrap();
}
