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

//! End-to-end tests for the `verify_proof` instruction. Unit tests are in
//! `verify_proof.rs`.
//!
//! Most follow the same shape: prove an inner circuit with a Poseidon
//! transcript, register its verifying key under a decider, then build an
//! outer ZKIR circuit that binds the proof with `inner_proof`, and verifies it
//! with `verify_proof`. Verifying the outer proof runs the pairing check on the
//! accumulator the instruction exposed.
//!
//!   * [`SingleScalarRelation`](verify_proof_common::SingleScalarRelation) and
//!     [`RsaSignatureRelation`] defer nothing: [`DeciderKind::None`].
//!   * [`RecursiveRelation`] verifies a
//!     [`SingleScalarRelation`](verify_proof_common::SingleScalarRelation) proof
//!     in-circuit, so it carries the accumulator that verification defers:
//!     [`DeciderKind::Collapsed`].
//!
//! Tests that build an outer circuit are `#[ignore]`d for runtime alone: they
//! prove circuits of k=18 and above, which takes minutes. They pass, and
//! `--ignored` runs them. Run them in release, or keygen looks hung:
//!
//! ```text
//! cargo test -p midnight-zkir --release --test verify_proof_e2e -- --ignored --test-threads=1
//! ```

#[path = "common/verify_proof.rs"]
mod verify_proof_common;

use std::any::type_name;
use std::io;
use std::ops::Range;
use std::ops::Rem;
use std::sync::OnceLock;
use std::time::Instant;

use group::Group;
use midnight_circuits::biguint::AssignedBigUint;
use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_circuits::instructions::{
    AssertionInstructions, AssignmentInstructions, PublicInputInstructions,
};
use midnight_circuits::types::{AssignedBit, AssignedNative};
use midnight_circuits::verifier::SelfEmulation;
use midnight_curves::{Bls12, Fq};
use midnight_proofs::circuit::{Layouter, Value};
use midnight_proofs::plonk;
use midnight_proofs::poly::kzg::KZGCommitmentScheme;
use midnight_proofs::transcript::{CircuitTranscript, Hashable, Sampleable, Transcript};
use midnight_zk_stdlib::{
    MidnightPK, MidnightVK, Relation, ZkStdLib, ZkStdLibArch, optimal_k, prove, setup_pk, setup_vk,
};
use midnight_zkir::IrSource;
use midnight_zkir::decider::{
    DeciderKind, accumulator_pis, deserialize_vk, serialize_vk, trivial_accumulator_pis,
};
use midnight_zkir::ir_instructions::verify_proof::{
    verify_proof_incircuit, verify_proof_offcircuit,
};
use num_bigint::BigUint;
use num_traits::{Num, One};
use rand_chacha::ChaCha20Rng;
use serialize::{Deserializable, Serializable};
use transient_crypto::curve::Fr;
use transient_crypto::proofs::{
    InnerProofWitness, InnerSelfEmulation, ParamsProver, Proof, ProofPreimage, ProverKey,
    TranscriptHash, VerifierKey, Zkir, accumulator_pi_len,
};

use crate::verify_proof_common::{
    BINDING_INPUT, InnerProof, inner_setup_at, inner_setup_for, load_ir, preimage_with,
    prove_inner_for, scalar_inner_proof, scalar_inner_proofs, srs, test_rng, vk_hash_hex, with_vks,
};

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

/// Statements for `collapsed_decider_catches_a_bad_carried_accumulator`.
const GOOD: u64 = 123;

const BOGUS: u64 = 456;

/// Width of the `Impact` in `impact_between_two_proofs_leaves_accumulators_intact`.
/// More than one, so padding a single slot would be caught.
const IMPACT_INPUTS: usize = 3;

/// The value that `Impact` discloses when guarded on.
const DISCLOSED: u64 = 42;

/// A larger domain than the RSA relation needs, giving it a different VK.
const OVERSIZED_K: u8 = 13;

/// RSA public exponent.
const E: u64 = 3;

/// Bit width of the RSA modulus, message and signature.
const NB_BITS: u32 = 1024;

/// Limb size of the BigUint gadget, in bits.
const LOG2_BASE: u32 = 96;

/// Cache for [`pinned_fixture`].
static PINNED: OnceLock<PinnedFixture> = OnceLock::new();

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

/// The accumulator is carried on the proof rather than in the statement, and
/// matches what off-circuit preparation computes.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn accumulator_is_carried_on_the_proof_not_the_statement() {
    let mut rng = test_rng();

    let fixture = pinned_fixture().await;
    let inner_proof = fixture.correct_proof(&mut rng);
    let inner_pis = fixture.inner_pis();

    let acc_len = accumulator_pi_len();
    assert_eq!(
        fixture.ir.accumulator_count(),
        1,
        "a single verify_proof exposes a single accumulator"
    );

    let preimage = outer_preimage(inner_proof.clone());
    let (outer_proof, outer_pis) =
        outer_prove(&fixture.ir, fixture.pk.clone(), &preimage, &mut rng).await;

    assert_eq!(
        outer_proof.accumulators.len(),
        1,
        "one verify_proof must carry exactly one accumulator block"
    );
    assert_eq!(
        outer_pis,
        vec![Fr::from(BINDING_INPUT)],
        "the statement is the binding input alone; the accumulator is not in it"
    );

    let expected = accumulator_pis(
        &verify_proof_offcircuit(&fixture.vk_blob, &inner_pis, &inner_proof, true)
            .expect("off-circuit preparation"),
    );
    assert_eq!(
        expected.len(),
        acc_len,
        "off-circuit accumulator should be acc_len field elements"
    );
    assert_eq!(
        outer_proof.accumulators[0].as_public_input(),
        expected,
        "the carried accumulator must match off-circuit preparation"
    );

    outer_verify(&fixture.vk, &outer_proof, outer_pis.clone());

    // Also with a deserialized key, as the ledger uses it.
    let mut bytes = Vec::new();
    Serializable::serialize(&fixture.vk, &mut bytes).expect("serialize vk");
    let reloaded: VerifierKey =
        Deserializable::deserialize(&mut &bytes[..], 0).expect("deserialize vk");
    outer_verify(&reloaded, &outer_proof, outer_pis);
}

/// An inner proof made with the Blake2b transcript instead of Poseidon is
/// rejected. Reading it with Poseidon does not error, so proving succeeds and
/// only the pairing catches it.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn blake2b_transcript_proof_is_rejected() {
    let mut rng = test_rng();

    let fixture = pinned_fixture().await;

    // As `prove_inner`, but with the wrong transcript.
    let proof = prove::<RsaSignatureRelation, TranscriptHash>(
        fixture.inner_srs.as_ref(),
        &fixture.inner_pk,
        &RsaSignatureRelation,
        &fixture.instance,
        fixture.signature.clone(),
        &mut rng,
    )
    .expect("inner prove (blake2b)");

    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        proof,
        &mut rng,
    )
    .await;

    assert_eq!(
        stage,
        Rejection::AtPairing,
        "a Blake2b proof must be caught by the pairing"
    );
}

/// A `Collapsed` decider checks the accumulator the inner proof carries, not
/// just the one from verifying it.
///
/// The recursive proof carries an accumulator for a proof of `BOGUS` checked
/// against `GOOD`. Everything is well-formed, so only the pairing on the folded
/// accumulator can reject it. The same proof under `None`, which ignores the
/// carried accumulator, is accepted.
#[actix_rt::test]
#[ignore = "slow: two levels of in-circuit verification"]
async fn collapsed_decider_catches_a_bad_carried_accumulator() {
    let mut rng = test_rng();

    let inner = scalar_inner_proofs(&[GOOD, BOGUS], &mut rng).await;
    let (good, bogus) = (&inner[0], &inner[1]);
    assert_eq!(
        good.vk_blob, bogus.vk_blob,
        "both proofs must be under one key"
    );

    // Preparation defers the pairing, so this succeeds.
    let deferred_bad = verify_proof_offcircuit(&good.vk_blob, &good.pis, &bogus.proof, true)
        .expect("preparation succeeds; only the deferred pairing could refuse this");

    let relation = RecursiveRelation {
        inner_vk: good.vk_blob.clone(),
    };
    let instance: Vec<Fq> = good
        .pis
        .iter()
        .copied()
        .chain(accumulator_pis(&deferred_bad))
        .collect();
    let (recursive_proof, recursive_vk) =
        prove_recursive(&relation, &instance, bogus.proof.clone(), &mut rng).await;

    let collapsed = serialize_vk(&recursive_vk, DeciderKind::Collapsed).expect("collapsed blob");
    let ir = outer_ir_for(&collapsed, &instance);
    let (pk, vk) = outer_keygen(&ir, "collapsed decider, bad carried accumulator").await;

    let (outer_proof, pis) =
        outer_prove(&ir, pk, &outer_preimage(recursive_proof.clone()), &mut rng).await;

    let err = vk
        .verify(&srs().verifier, &outer_proof, pis.into_iter())
        .expect_err("a carried accumulator that does not pair must be rejected");
    assert!(
        format!("{err:#}").contains("pairing"),
        "must fail at the pairing, not the PLONK check: {err:#}"
    );

    // Control: `None` ignores the carried accumulator, so this passes.
    let none = serialize_vk(&recursive_vk, DeciderKind::None).expect("none blob");
    let ir_none = outer_ir_for(&none, &instance);
    let (pk_none, vk_none) = outer_keygen(&ir_none, "none decider, same recursive proof").await;
    let (proof, pis) = outer_prove(
        &ir_none,
        pk_none,
        &outer_preimage(recursive_proof),
        &mut rng,
    )
    .await;
    outer_verify(&vk_none, &proof, pis);
}

/// A corrupted proof is rejected: in preparation if a commitment no longer
/// decodes, at the pairing if a scalar is changed to another valid value.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn corrupted_proof_is_rejected() {
    let mut rng = test_rng();

    let fixture = pinned_fixture().await;
    let proof = fixture.correct_proof(&mut rng);
    let reads = proof_reads(&fixture.vk_blob, &fixture.inner_pis(), &proof);
    let is_scalar = |ty: &str| ty == type_name::<Fq>();

    let commitment = reads
        .iter()
        .find(|(_, ty)| !is_scalar(ty))
        .expect("the proof has a commitment")
        .0
        .clone();
    let mut structural = proof.clone();
    structural[commitment.start] ^= 0x01;
    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        structural,
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPreparation,
        "a corrupted commitment must fail to decode"
    );

    // Changed through its decoded value, so it still decodes.
    let scalar = reads
        .iter()
        .find(|(_, ty)| is_scalar(ty))
        .expect("the proof has a scalar")
        .0
        .clone();
    let value = <Fq as Hashable<PoseidonState<Fq>>>::read(&mut &proof[scalar.clone()])
        .expect("decode scalar");
    let mut semantic = proof.clone();
    semantic[scalar].copy_from_slice(&<Fq as Hashable<PoseidonState<Fq>>>::to_bytes(
        &(value + Fq::from(1u64)),
    ));
    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        semantic,
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPairing,
        "a changed scalar must be caught by the pairing"
    );
}

/// Guarded off, `verify_proof` exposes the trivial accumulator whatever the
/// witness bytes are.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn guarded_off_verify_proof_is_witness_independent() {
    let mut rng = test_rng();
    let inner = scalar_inner_proof(&mut rng).await;
    let ir = shared_guard_ir(&inner);
    let (pk, vk) = outer_keygen(&ir, "shared guard, off").await;

    let trivial = trivial_accumulator_pis();

    // Same length as a real proof, so no size check can tell them apart.
    let garbage = vec![0xABu8; inner.proof.len()];
    assert_ne!(garbage, inner.proof, "the two witnesses must differ");

    for (label, witness) in [
        ("a genuine inner proof", inner.proof.clone()),
        ("bytes that are not a proof", garbage),
    ] {
        println!("--- guarded off, witness: {label} ---");

        let preimage = outer_preimage_with(vec![witness], vec![Fr::from(0u64)], vec![]);
        let (proof, pis) = outer_prove(&ir, pk.clone(), &preimage, &mut rng).await;

        assert_eq!(
            proof.accumulators.len(),
            1,
            "{label}: a guarded-off verify_proof still occupies its block"
        );
        assert_eq!(
            proof.accumulators[0].as_public_input(),
            trivial,
            "{label}: the exposed accumulator must be the trivial one"
        );

        outer_verify(&vk, &proof, pis);
    }
}

/// Two `verify_proof`s over different keys, with an `Impact` between them
/// guarded on or off, both verify, with accumulators intact and out of the
/// statement.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn impact_between_two_proofs_leaves_accumulators_intact() {
    let mut rng = test_rng();

    let inner = [
        rsa_inner_proof(&mut rng).await,
        scalar_inner_proof(&mut rng).await,
    ];
    assert_ne!(
        inner[0].vk_blob, inner[1].vk_blob,
        "the two keys must differ"
    );
    let ir = interleaved_ir(&inner[0], &inner[1]);

    assert_eq!(
        ir.accumulator_count(),
        2,
        "two verify_proof instructions expose two accumulators, Impact or not"
    );

    let (pk, vk) = outer_keygen(&ir, "2 verify_proof, 1 interleaved impact").await;

    for guard in [true, false] {
        println!("--- guard {} ---", if guard { "on" } else { "off" });

        // Guarded off, the `Impact` publishes zeros and consumes no transcript.
        let (inputs, transcript, expected_middle) = if guard {
            (
                vec![Fr::from(1u64)],
                vec![Fr::from(DISCLOSED); IMPACT_INPUTS],
                Fr::from(DISCLOSED),
            )
        } else {
            (vec![Fr::from(0u64)], vec![], Fr::from(0u64))
        };

        let preimage = outer_preimage_with(
            inner.iter().map(|i| i.proof.clone()).collect(),
            inputs,
            transcript,
        );
        let (proof, pis, skips) =
            outer_prove_with_skips(&ir, pk.clone(), &preimage, &mut rng).await;

        // Skips index the statement with accumulators removed, so
        // `verify_proof` must not add any.
        let expected_skips = if guard {
            vec![None]
        } else {
            vec![Some(IMPACT_INPUTS)]
        };
        assert_eq!(
            skips, expected_skips,
            "guard {guard}: one skip entry per Impact, none per verify_proof"
        );

        assert_eq!(
            proof.accumulators.len(),
            2,
            "guard {guard}: both accumulators must be carried"
        );
        assert_eq!(
            pis.len(),
            1 + IMPACT_INPUTS,
            "guard {guard}: the statement is the binding input plus the Impact's slots"
        );
        assert_eq!(
            pis[0],
            Fr::from(BINDING_INPUT),
            "guard {guard}: no accumulator field leaked into the statement"
        );

        let middle = &pis[1..1 + IMPACT_INPUTS];
        assert!(
            middle.iter().all(|f| *f == expected_middle),
            "guard {guard}: the interleaved slots should all be {expected_middle:?}, got {middle:?}"
        );

        for (i, inner) in inner.iter().enumerate() {
            let want = accumulator_pis(
                &verify_proof_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
                    .expect("off-circuit preparation"),
            );
            assert_eq!(
                proof.accumulators[i].as_public_input(),
                want,
                "guard {guard}: accumulator {i} must match off-circuit preparation"
            );
        }

        outer_verify(&vk, &proof, pis);
    }
}

/// A proof made under a different verifying key is rejected. The same relation
/// in a larger domain gives a same-length proof, caught by the pairing; a
/// different relation fails in preparation.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn proof_from_another_vk_is_rejected() {
    let mut rng = test_rng();

    let fixture = pinned_fixture().await;
    let correct_proof = fixture.correct_proof(&mut rng);

    let (oversized_srs, oversized_pk, oversized_vk) =
        inner_setup_at::<RsaSignatureRelation>("rsa, oversized domain", OVERSIZED_K).await;
    assert_ne!(
        fixture.vk_blob, oversized_vk,
        "setting the same relation up at a different k must give a different VK"
    );
    let wrong_size_proof = prove_inner(
        &fixture.instance,
        fixture.signature.clone(),
        &oversized_pk,
        &oversized_srs,
        &mut rng,
    );

    let substituted_proof = scalar_inner_proof(&mut rng).await.proof;

    assert_eq!(
        wrong_size_proof.len(),
        correct_proof.len(),
        "only the key should differ, not the proof length"
    );
    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        wrong_size_proof,
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPairing,
        "a proof under the wrong key must be caught by the pairing"
    );

    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        substituted_proof,
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPreparation,
        "a proof of another relation must fail in preparation"
    );
}

/// Two `verify_proof`s sharing one key, with one side-table entry, both verify.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn same_vk_verified_twice_is_accepted() {
    let mut rng = test_rng();

    // Scalar proofs: two RSA verifications would need k=20.
    let inner = scalar_inner_proofs(&[123, 456], &mut rng).await;
    assert_eq!(
        inner[0].vk_blob, inner[1].vk_blob,
        "both proofs must be under the same key"
    );
    assert_ne!(
        inner[0].pis, inner[1].pis,
        "the two statements must differ, or verifying one twice would pass"
    );

    let entries: Vec<_> = inner.iter().map(|i| i.entry()).collect();
    let (outer_ir, outer_pk, outer_vk) = outer_setup_all(&entries).await;
    assert_eq!(
        outer_ir.verify_proof_vks.len(),
        1,
        "the side-table must hold one entry for a key used twice"
    );
    assert_eq!(
        outer_ir.accumulator_count(),
        2,
        "two instructions still expose two accumulators"
    );

    let preimage = outer_preimage_all(inner.iter().map(|i| i.proof.clone()).collect());
    let (outer_proof, outer_pis) = outer_prove(&outer_ir, outer_pk, &preimage, &mut rng).await;

    // Each accumulator must come from its own proof, not the first one reused.
    assert_eq!(outer_proof.accumulators.len(), 2);
    for (i, inner) in inner.iter().enumerate() {
        let want = accumulator_pis(
            &verify_proof_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
                .expect("off-circuit preparation"),
        );
        assert_eq!(
            outer_proof.accumulators[i].as_public_input(),
            want,
            "accumulator {i} must match its own inner proof"
        );
    }

    outer_verify(&outer_vk, &outer_proof, outer_pis);
}

/// A valid proof of a different statement is rejected. Proving succeeds, so
/// only the pairing catches it.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn valid_proof_of_other_statement_is_rejected() {
    let mut rng = test_rng();

    let fixture = pinned_fixture().await;

    let (modulus, d) = rsa_key();
    let msg_b = message(&modulus, 1);
    assert_ne!(fixture.instance.1, msg_b, "the two messages must differ");
    let instance_b = (modulus.clone(), msg_b.clone());
    let sig_b = sign(&msg_b, &d, &modulus);
    let proof_b = prove_inner(
        &instance_b,
        sig_b,
        &fixture.inner_pk,
        &fixture.inner_srs,
        &mut rng,
    );

    let stage = expect_rejected(
        &fixture.ir,
        fixture.pk.clone(),
        &fixture.vk,
        &fixture.vk_blob,
        &fixture.inner_pis(),
        proof_b,
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPairing,
        "a proof of the wrong statement must be caught by the pairing"
    );
}

/// An `instance` of the wrong length for its key is rejected. Neither `check`
/// nor proving checks the length, so only the pairing catches it.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn wrong_length_instance_is_rejected() {
    let mut rng = test_rng();
    let inner = rsa_inner_proof(&mut rng).await;
    assert!(
        inner.pis.len() > 1,
        "truncating must not reduce to an empty instance"
    );

    // One element short. Too long would need another keygen and fails the
    // same way.
    let instance = inner.pis[..inner.pis.len() - 1].to_vec();
    let ir = outer_ir_for(&inner.vk_blob, &instance);

    let (pk, vk) = outer_keygen(&ir, "wrong-length instance, one short").await;
    let stage = expect_rejected(
        &ir,
        pk,
        &vk,
        &inner.vk_blob,
        &instance,
        inner.proof.clone(),
        &mut rng,
    )
    .await;
    assert_eq!(
        stage,
        Rejection::AtPairing,
        "both passes agree on the wrong length, so only the pairing can refuse it"
    );

    ir.check(&outer_preimage(inner.proof.clone()))
        .expect("check does not validate the instance length");
}

/// An inner proof that defers nothing of its own.
#[actix_rt::test]
#[ignore = "slow: builds and proves a high-k outer circuit"]
async fn verify_proof_without_a_decider() {
    let mut rng = test_rng();
    let inner = scalar_inner_proof(&mut rng).await;

    let ir = witnessed_outer_ir(&inner.vk_blob, inner.pis.len());
    // One accumulator, whatever the decider kind. That is what keeps the
    // exposed shape witness-independent and computable at keygen.
    assert_eq!(ir.accumulator_count(), 1);
    let (pk, vk) = outer_keygen(&ir, "none decider, guarded").await;

    // Proving already runs both `verify_proof` passes, so it fails if the inner
    // proof does not check out; verifying then discharges the accumulator that
    // verification deferred.
    let preimage = witnessed_outer_preimage(true, &inner.proof, &inner.pis);
    let (proof, pis) = outer_prove(&ir, pk.clone(), &preimage, &mut rng).await;
    outer_verify(&vk, &proof, pis);

    // Guarded off, with no inner proof and no instance supplied, the exposed
    // accumulator is the trivial one, whose pairing holds by construction.
    let (guarded, guarded_pis) = outer_prove(
        &ir,
        pk,
        &witnessed_outer_preimage(false, &[], &[]),
        &mut rng,
    )
    .await;
    assert_eq!(
        guarded.accumulators[0].as_public_input(),
        trivial_accumulator_pis(),
    );
    outer_verify(&vk, &guarded, guarded_pis);
}

/// An inner proof carrying an accumulator of its own, which the instruction
/// folds into the one it exposes.
#[actix_rt::test]
#[ignore = "slow: two levels of in-circuit verification"]
async fn verify_proof_with_a_collapsed_decider() {
    let mut rng = test_rng();

    // The proof to be verified in-circuit, and the accumulator verifying it
    // defers.
    let inner = scalar_inner_proof(&mut rng).await;
    let deferred = accumulator_pis(
        &verify_proof_offcircuit(&inner.vk_blob, &inner.pis, &inner.proof, true)
            .expect("the accumulator the scalar proof defers"),
    );

    // The proof that verifies it, carrying that accumulator in its instance
    // tail.
    let relation = RecursiveRelation {
        inner_vk: inner.vk_blob.clone(),
    };
    let instance: Vec<Fq> = inner.pis.iter().copied().chain(deferred).collect();
    let (proof, recursive_vk) =
        prove_recursive(&relation, &instance, inner.proof.clone(), &mut rng).await;

    let collapsed = serialize_vk(&recursive_vk, DeciderKind::Collapsed).expect("collapsed blob");
    let ir = witnessed_outer_ir(&collapsed, instance.len());
    assert_eq!(ir.accumulator_count(), 1);
    let (pk, vk) = outer_keygen(&ir, "collapsed decider, guarded").await;

    let preimage = witnessed_outer_preimage(true, &proof, &instance);
    let (outer_proof, pis) = outer_prove(&ir, pk.clone(), &preimage, &mut rng).await;

    // What the instruction exposed is the fold, not the recursive proof's own
    // accumulator: the carried one is in there too.
    let own = accumulator_pis(
        &verify_proof_offcircuit(
            &serialize_vk(&recursive_vk, DeciderKind::None).expect("none blob"),
            &instance,
            &proof,
            true,
        )
        .expect("the recursive proof's own accumulator"),
    );
    assert_ne!(
        outer_proof.accumulators[0].as_public_input(),
        own,
        "the carried accumulator must have been folded in"
    );

    // One pairing, discharging both.
    outer_verify(&vk, &outer_proof, pis);

    // Guarded off, as above: the trivial accumulator, and no witnesses at all.
    let (guarded, guarded_pis) = outer_prove(
        &ir,
        pk,
        &witnessed_outer_preimage(false, &[], &[]),
        &mut rng,
    )
    .await;
    assert_eq!(
        guarded.accumulators[0].as_public_input(),
        trivial_accumulator_pis(),
    );
    outer_verify(&vk, &guarded, guarded_pis);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

/// One `inner_proof` / `verify_proof` pair behind the input guard `%g`.
fn shared_guard_ir(inner: &InnerProof) -> IrSource {
    let instructions = format!(
        r#"{{ "op": "inner_proof", "guard": "%g", "output": "%p_0" }},
           {{ "op": "verify_proof", "guard": "%g", "vk_hash": "0x{hash}",
              "instance": [{instance}], "proof": "%p_0" }}"#,
        hash = vk_hash_hex(&inner.vk_blob),
        instance = instance_json(&inner.pis),
    );
    outer_ir_with(
        r#"{ "name": "%g", "type": "Scalar<BLS12-381>" }"#,
        false,
        &instructions,
        vec![inner.vk_blob.clone()],
    )
}

/// Two `verify_proof`s with an `Impact` between them, guarded by the circuit's
/// one input `%v_0`.
fn interleaved_ir(a: &InnerProof, b: &InnerProof) -> IrSource {
    let impact_operands = vec![format!(r#""0x{DISCLOSED:02x}""#); IMPACT_INPUTS].join(", ");
    let instructions = format!(
        r#"{{ "op": "inner_proof", "guard": "0x01", "output": "%p_0" }},
           {{ "op": "inner_proof", "guard": "0x01", "output": "%p_1" }},
           {{
               "op": "verify_proof",
               "guard": "0x01",
               "vk_hash": "0x{hash_a}",
               "instance": [{instance_a}],
               "proof": "%p_0"
           }},
           {{ "op": "impact", "guard": "%v_0", "inputs": [{impact_operands}] }},
           {{
               "op": "verify_proof",
               "guard": "0x01",
               "vk_hash": "0x{hash_b}",
               "instance": [{instance_b}],
               "proof": "%p_1"
           }}"#,
        hash_a = vk_hash_hex(&a.vk_blob),
        hash_b = vk_hash_hex(&b.vk_blob),
        instance_a = instance_json(&a.pis),
        instance_b = instance_json(&b.pis),
    );
    outer_ir_with(
        r#"{ "name": "%v_0", "type": "Scalar<BLS12-381>" }"#,
        false,
        &instructions,
        vec![a.vk_blob.clone(), b.vk_blob.clone()],
    )
}

/// The byte range and type of each value read while preparing `proof`.
fn proof_reads(vk_blob: &[u8], instance: &[Fq], proof: &[u8]) -> Vec<(Range<usize>, &'static str)> {
    let (_, vk) = deserialize_vk(vk_blob).expect("inner vk");
    let mut transcript = RecordingTranscript::init_from_bytes(proof);
    plonk::prepare::<Fq, KZGCommitmentScheme<Bls12>, RecordingTranscript>(
        vk.vk(),
        &[&[<InnerSelfEmulation as SelfEmulation>::C::identity()]],
        &[&[instance]],
        &mut transcript,
    )
    .expect("prepare a valid proof");
    transcript.reads
}

/// A Poseidon transcript that records where each value it reads came from.
#[derive(Clone)]
struct RecordingTranscript {
    inner: CircuitTranscript<PoseidonState<Fq>>,
    reads: Vec<(Range<usize>, &'static str)>,
}

impl Transcript for RecordingTranscript {
    type Hash = PoseidonState<Fq>;

    fn init() -> Self {
        Self {
            inner: CircuitTranscript::init(),
            reads: Vec::new(),
        }
    }

    fn init_from_bytes(bytes: &[u8]) -> Self {
        Self {
            inner: CircuitTranscript::init_from_bytes(bytes),
            reads: Vec::new(),
        }
    }

    fn squeeze_challenge<T: Sampleable<Self::Hash>>(&mut self) -> T {
        self.inner.squeeze_challenge()
    }

    fn common<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.inner.common(input)
    }

    fn read<T: Hashable<Self::Hash>>(&mut self) -> io::Result<T> {
        let start = self.inner.buffer().position() as usize;
        let value = self.inner.read()?;
        let end = self.inner.buffer().position() as usize;
        self.reads.push((start..end, type_name::<T>()));
        Ok(value)
    }

    fn write<T: Hashable<Self::Hash>>(&mut self, input: &T) -> io::Result<()> {
        self.inner.write(input)
    }

    fn finalize(self) -> Vec<u8> {
        self.inner.finalize()
    }

    fn assert_empty(&mut self) -> io::Result<()> {
        self.inner.assert_empty()
    }
}

type Modulus = BigUint;

type Message = BigUint;

type Signature = BigUint;

/// Proves knowledge of an RSA signature `s` with `s^3 = msg (mod m)`, for public
/// `m` and `msg`.
#[derive(Clone, Default)]
struct RsaSignatureRelation;

impl Relation for RsaSignatureRelation {
    type Instance = (Modulus, Message);
    type Witness = Signature;
    type Error = plonk::Error;

    fn format_instance((pk, msg): &Self::Instance) -> Result<Vec<Fq>, plonk::Error> {
        Ok([
            AssignedBigUint::<Fq>::as_public_input(pk, NB_BITS),
            AssignedBigUint::<Fq>::as_public_input(msg, NB_BITS),
        ]
        .into_iter()
        .flatten()
        .collect())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        instance: Value<Self::Instance>,
        witness: Value<Self::Witness>,
    ) -> Result<(), plonk::Error> {
        let biguint = std_lib.biguint();

        let public_key = biguint.assign_biguint(
            layouter,
            instance.as_ref().map(|(pk, _)| pk.clone()),
            NB_BITS,
        )?;
        let message = biguint.assign_biguint(layouter, instance.map(|(_, msg)| msg), NB_BITS)?;
        let signature = biguint.assign_biguint(layouter, witness, NB_BITS)?;

        biguint.constrain_as_public_input(layouter, &public_key, NB_BITS)?;
        biguint.constrain_as_public_input(layouter, &message, NB_BITS)?;

        let expected_msg = biguint.mod_exp(layouter, &signature, E, &public_key)?;

        biguint.assert_equal(layouter, &message, &expected_msg)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            nr_pow2range_cols: 4,
            ..ZkStdLibArch::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, _writer: &mut W) -> std::io::Result<()> {
        Ok(())
    }

    fn read_relation<R: std::io::Read>(_reader: &mut R) -> std::io::Result<Self> {
        Ok(RsaSignatureRelation)
    }
}

/// Verifies a proof of `inner_vk` in-circuit, and exposes the accumulator that
/// verification defers as the tail of its own instance.
#[derive(Clone)]
struct RecursiveRelation {
    /// The verifying key of the proof this one verifies, as registered:
    /// `serialize_vk`'s blob.
    pub inner_vk: Vec<u8>,
}

impl Relation for RecursiveRelation {
    type Instance = Vec<Fq>;
    type Witness = Vec<u8>;
    type Error = plonk::Error;

    fn format_instance(instance: &Vec<Fq>) -> Result<Vec<Fq>, plonk::Error> {
        Ok(instance.clone())
    }

    fn circuit(
        &self,
        std_lib: &ZkStdLib,
        layouter: &mut impl Layouter<Fq>,
        instance: Value<Vec<Fq>>,
        witness: Value<Vec<u8>>,
    ) -> Result<(), plonk::Error> {
        let x: AssignedNative<Fq> = std_lib.assign(layouter, instance.map(|fields| fields[0]))?;
        std_lib.constrain_as_public_input(layouter, &x)?;

        // Verifying it constrains the deferred accumulator as the rest of our
        // public inputs. Nothing here is guarded, so the guard is a fixed one.
        let on: AssignedBit<Fq> = std_lib.assign_fixed(layouter, true)?;
        verify_proof_incircuit(std_lib, layouter, &self.inner_vk, &[&[x]], witness, &on)
    }

    fn used_chips(&self) -> ZkStdLibArch {
        ZkStdLibArch {
            poseidon: true,
            bls12_381: true,
            nr_pow2range_cols: 4,
            ..Default::default()
        }
    }

    fn write_relation<W: std::io::Write>(&self, writer: &mut W) -> std::io::Result<()> {
        writer.write_all(&(self.inner_vk.len() as u64).to_le_bytes())?;
        writer.write_all(&self.inner_vk)
    }

    fn read_relation<R: std::io::Read>(reader: &mut R) -> std::io::Result<Self> {
        let mut len = [0u8; 8];
        reader.read_exact(&mut len)?;
        let mut inner_vk = vec![0u8; u64::from_le_bytes(len) as usize];
        reader.read_exact(&mut inner_vk)?;
        Ok(RecursiveRelation { inner_vk })
    }
}

/// Keygen and prove [`RecursiveRelation`], with the Poseidon transcript the
/// in-circuit verifier expects. Not [`prove_inner_for`], which needs
/// `R: Default`.
async fn prove_recursive(
    relation: &RecursiveRelation,
    instance: &Vec<Fq>,
    witness: Vec<u8>,
    rng: &mut ChaCha20Rng,
) -> (Vec<u8>, MidnightVK) {
    let k = optimal_k(relation) as u8;
    println!("recursive circuit k = {k}");
    let srs = srs().params_for(k);
    let vk = setup_vk(srs.as_ref(), relation);
    let pk = setup_pk(relation, &vk);
    let proof = prove::<RecursiveRelation, PoseidonState<Fq>>(
        srs.as_ref(),
        &pk,
        relation,
        instance,
        witness,
        rng,
    )
    .expect("recursive prove");
    println!("recursive prove: {} proof bytes", proof.len());
    (proof, vk)
}

/// A fixed RSA key: the modulus and the private exponent. The primes are from
/// the `midnight-zk` RSA example.
fn rsa_key() -> (Modulus, BigUint) {
    let p = BigUint::from_str_radix(
        "81e05798232330a8c7059621c812dc9d2bba37edbd0e79f101eef1db373c1272\
         4595480ae6a9dbbf158fa65d6910b8aea7b3be2eede9123ede8d84ec9e8ee907",
        16,
    )
    .unwrap();
    let q = BigUint::from_str_radix(
        "acd6fd3c0d70502e8ecefb20259fbf4783a614a0fb1a33701e3adc84947326a7\
         54f8a632e5f6cd718a681cde953024b3612bb0646f180b6fd063b1ef4e10d4a5",
        16,
    )
    .unwrap();

    let modulus = &p * &q;
    let phi = (&p - BigUint::one()) * (&q - BigUint::one());
    let d = BigUint::from(E)
        .modinv(&phi)
        .expect("e must be invertible mod phi");

    (modulus, d)
}

/// A fixed message reduced mod `modulus`; `tag` selects which.
fn message(modulus: &Modulus, tag: u8) -> Message {
    let hex = format!(
        "6d69646e696768742d6c65646765722d7273612d696e6e65722d70726f6f662d\
         746573742d766563746f722d646f2d6e6f742d7573652d696e2d70726f64{tag:02x}"
    );
    BigUint::from_str_radix(&hex, 16).unwrap().rem(modulus)
}

/// RSA-signs `msg` with private exponent `d`.
fn sign(msg: &Message, d: &BigUint, modulus: &Modulus) -> Signature {
    let signature = msg.modpow(d, modulus);
    debug_assert_eq!(&signature.modpow(&BigUint::from(E), modulus), msg);
    signature
}

/// The RSA statement and signature used by [`pinned_fixture`].
fn pinned_statement() -> ((Modulus, Message), Signature) {
    let (modulus, d) = rsa_key();
    let msg = message(&modulus, 0);
    let signature = sign(&msg, &d, &modulus);
    ((modulus, msg), signature)
}

/// [`inner_setup_for`] for [`RsaSignatureRelation`].
async fn inner_setup() -> (ParamsProver, MidnightPK<RsaSignatureRelation>, Vec<u8>) {
    inner_setup_for::<RsaSignatureRelation>("rsa").await
}

/// [`prove_inner_for`] for [`RsaSignatureRelation`].
fn prove_inner(
    instance: &(Modulus, Message),
    signature: Signature,
    inner_pk: &MidnightPK<RsaSignatureRelation>,
    inner_srs: &ParamsProver,
    rng: &mut ChaCha20Rng,
) -> Vec<u8> {
    prove_inner_for::<RsaSignatureRelation>("rsa", instance, signature, inner_pk, inner_srs, rng)
}

/// `pis` as `verify_proof` instance operands. Immediates are little-endian hex.
fn instance_json(pis: &[Fq]) -> String {
    pis.iter()
        .map(|f| format!("\"0x{}\"", const_hex::encode(Fr(*f).as_le_bytes())))
        .collect::<Vec<_>>()
        .join(", ")
}

/// The outer IR, with the side-table attached.
fn outer_ir_with(
    inputs: &str,
    do_communications_commitment: bool,
    instructions: &str,
    vks: Vec<Vec<u8>>,
) -> IrSource {
    with_vks(
        load_ir(inputs, do_communications_commitment, instructions),
        vks,
    )
}

/// [`outer_ir_with`] with no inputs and no commitment.
fn outer_ir(instructions: &str, vks: Vec<Vec<u8>>) -> IrSource {
    outer_ir_with("", false, instructions, vks)
}

/// An RSA proof of [`pinned_statement`].
async fn rsa_inner_proof(rng: &mut ChaCha20Rng) -> InnerProof {
    let (srs, pk, vk_blob) = inner_setup().await;
    let (instance, signature) = pinned_statement();
    let proof = prove_inner(&instance, signature, &pk, &srs, rng);
    let pis = RsaSignatureRelation::format_instance(&instance).expect("format rsa instance");
    InnerProof {
        vk_blob,
        pis,
        proof,
    }
}

/// One `inner_proof` per entry, then one `verify_proof` per entry.
fn outer_ir_for_all(entries: &[(Vec<u8>, Vec<Fq>)]) -> IrSource {
    let bindings = (0..entries.len())
        .map(|i| format!(r#"{{ "op": "inner_proof", "guard": "0x01", "output": "%p_{i}" }}"#))
        .collect::<Vec<_>>();

    let verifications = entries.iter().enumerate().map(|(i, (vk_blob, pis))| {
        format!(
            r#"{{
                   "op": "verify_proof",
                   "guard": "0x01",
                   "vk_hash": "0x{vk_hash}",
                   "instance": [{instance}],
                   "proof": "%p_{i}"
               }}"#,
            vk_hash = vk_hash_hex(vk_blob),
            instance = instance_json(pis),
        )
    });

    let instructions = bindings
        .into_iter()
        .chain(verifications)
        .collect::<Vec<_>>()
        .join(",\n               ");

    // A blob listed twice is rejected, so shared keys get one entry.
    let mut vks: Vec<Vec<u8>> = Vec::new();
    for (blob, _) in entries {
        if !vks.contains(blob) {
            vks.push(blob.clone());
        }
    }

    outer_ir(&instructions, vks)
}

/// [`outer_ir_for_all`] for one proof.
fn outer_ir_for(vk_blob: &[u8], inner_pis: &[Fq]) -> IrSource {
    outer_ir_for_all(&[(vk_blob.to_vec(), inner_pis.to_vec())])
}

/// Builds [`outer_ir_for_all`] and runs keygen.
async fn outer_setup_all(
    entries: &[(Vec<u8>, Vec<Fq>)],
) -> (IrSource, ProverKey<IrSource>, VerifierKey) {
    let ir = outer_ir_for_all(entries);
    let label = format!("{} verify_proof instruction(s)", entries.len());
    let (pk, vk) = outer_keygen(&ir, &label).await;
    (ir, pk, vk)
}

/// Outer keygen, printing `k` and timing.
async fn outer_keygen(ir: &IrSource, label: &str) -> (ProverKey<IrSource>, VerifierKey) {
    println!("outer circuit k = {} ({label})", ir.k());

    let t = Instant::now();
    let (pk, vk) = ir.keygen(srs()).await.expect("outer keygen");
    println!("outer keygen: {:.1?}", t.elapsed());

    (pk, vk)
}

/// Builds the outer circuit for one RSA proof of `instance` and runs keygen.
async fn outer_setup(
    vk_blob: Vec<u8>,
    instance: &(Modulus, Message),
) -> (IrSource, ProverKey<IrSource>, VerifierKey) {
    let inner_pis = RsaSignatureRelation::format_instance(instance).expect("format inner instance");
    assert_eq!(
        inner_pis.len(),
        2 * NB_BITS.div_ceil(LOG2_BASE) as usize,
        "expected 11 limbs each for modulus and message"
    );
    outer_setup_all(&[(vk_blob, inner_pis)]).await
}

/// A single-RSA-proof outer circuit and its keys, shared across tests because
/// keygen is slow.
struct PinnedFixture {
    pub inner_srs: ParamsProver,
    pub inner_pk: MidnightPK<RsaSignatureRelation>,
    pub vk_blob: Vec<u8>,
    pub instance: (Modulus, Message),
    pub signature: Signature,
    pub ir: IrSource,
    pub pk: ProverKey<IrSource>,
    pub vk: VerifierKey,
}

/// The shared [`PinnedFixture`], built on first use. Concurrent first calls
/// would each build one; harmless, and the suite runs single-threaded.
async fn pinned_fixture() -> &'static PinnedFixture {
    if let Some(fixture) = PINNED.get() {
        println!("(reusing the pinned outer circuit)");
        return fixture;
    }

    let (inner_srs, inner_pk, vk_blob) = inner_setup().await;
    let (instance, signature) = pinned_statement();
    let (ir, pk, vk) = outer_setup(vk_blob.clone(), &instance).await;

    let _ = PINNED.set(PinnedFixture {
        inner_srs,
        inner_pk,
        vk_blob,
        instance,
        signature,
        ir,
        pk,
        vk,
    });
    PINNED.get().expect("just set")
}

impl PinnedFixture {
    /// A fresh valid proof of [`pinned_statement`].
    pub fn correct_proof(&self, rng: &mut ChaCha20Rng) -> Vec<u8> {
        prove_inner(
            &self.instance,
            self.signature.clone(),
            &self.inner_pk,
            &self.inner_srs,
            rng,
        )
    }

    /// The inner public inputs.
    pub fn inner_pis(&self) -> Vec<Fq> {
        RsaSignatureRelation::format_instance(&self.instance).expect("format inner instance")
    }
}

/// A preimage carrying `inner_proofs` and nothing else.
fn outer_preimage_all(inner_proofs: Vec<Vec<u8>>) -> ProofPreimage {
    preimage_with(
        inner_proofs
            .into_iter()
            .map(InnerProofWitness::Direct)
            .collect(),
    )
}

/// [`outer_preimage_all`] for one proof.
fn outer_preimage(inner_proof: Vec<u8>) -> ProofPreimage {
    outer_preimage_all(vec![inner_proof])
}

/// [`outer_preimage_all`] with circuit inputs and public transcript inputs. A
/// guarded-on `Impact` needs one transcript entry per operand, matching its
/// value; guarded off it needs none.
fn outer_preimage_with(
    inner_proofs: Vec<Vec<u8>>,
    inputs: Vec<Fr>,
    public_transcript_inputs: Vec<Fr>,
) -> ProofPreimage {
    let mut preimage = outer_preimage_all(inner_proofs);
    preimage.inputs = inputs;
    preimage.public_transcript_inputs = public_transcript_inputs;
    preimage
}

/// The outer ZKIR circuit: witness the inner proof's `instance_len` public
/// inputs, bind the proof, verify it.
///
/// ZKIR has no instruction of its own for the inner instance: the fields are
/// ordinary prover witnesses, and `verify_proof` just names the variables they
/// were bound to. Here that is one guarded `private_input` per field, which is
/// what a caller emits; the values travel in `ProofPreimage::private_transcript`.
///
/// Everything is under the input guard `%g`, so one keygen serves both guard
/// values — the guard changes what the accumulator public inputs are, never the
/// shape of the circuit.
fn witnessed_outer_ir(vk_blob: &[u8], instance_len: usize) -> IrSource {
    let names: Vec<String> = (0..instance_len).map(|i| format!("\"%i_{i}\"")).collect();
    let witnesses = names.iter().map(|name| {
        format!(
            r#"{{ "op": "private_input", "guard": "%g",
                  "type": "Scalar<BLS12-381>", "output": {name} }}"#
        )
    });
    let pair = [
        r#"{ "op": "inner_proof", "guard": "%g", "output": "%p" }"#.to_string(),
        format!(
            r#"{{ "op": "verify_proof", "guard": "%g", "vk_hash": "0x{hash}",
                  "instance": [{names}], "proof": "%p" }}"#,
            hash = vk_hash_hex(vk_blob),
            names = names.join(", "),
        ),
    ];
    let instructions = witnesses
        .chain(pair)
        .collect::<Vec<_>>()
        .join(",\n               ");
    outer_ir_with(
        r#"{ "name": "%g", "type": "Scalar<BLS12-381>" }"#,
        false,
        &instructions,
        vec![vk_blob.to_vec()],
    )
}

/// The outer proof's preimage for [`witnessed_outer_ir`]. Guarded off, there is
/// no inner proof and no inner instance to supply at all.
fn witnessed_outer_preimage(guard: bool, proof: &[u8], instance: &[Fq]) -> ProofPreimage {
    let (proof, instance) = if guard {
        (proof.to_vec(), instance.iter().copied().map(Fr).collect())
    } else {
        (vec![], vec![])
    };
    // One slot for the circuit's single `inner_proof`, whatever the guard;
    // blank where it is off.
    let mut preimage = outer_preimage_with(vec![proof], vec![Fr::from(guard as u64)], vec![]);
    // The inner instance, as ordinary prover witnesses.
    preimage.private_transcript = instance;
    preimage
}

/// Proves the outer circuit, printing timing.
async fn outer_prove(
    ir: &IrSource,
    pk: ProverKey<IrSource>,
    preimage: &ProofPreimage,
    rng: &mut ChaCha20Rng,
) -> (Proof, Vec<Fr>) {
    let (proof, pis, _skips) = outer_prove_with_skips(ir, pk, preimage, rng).await;
    (proof, pis)
}

/// As [`outer_prove`], also returning the public-input skips: one per `Impact`,
/// `Some(n)` when it was guarded off.
async fn outer_prove_with_skips(
    ir: &IrSource,
    pk: ProverKey<IrSource>,
    preimage: &ProofPreimage,
    rng: &mut ChaCha20Rng,
) -> (Proof, Vec<Fr>, Vec<Option<usize>>) {
    let t = Instant::now();
    let (proof, pis, skips) = ir
        .prove(rng, srs(), pk, preimage)
        .await
        .expect("outer prove");
    println!("outer prove: {:.1?} (pi skips: {skips:?})", t.elapsed());
    (proof, pis, skips)
}

/// Verifies the outer proof, including the pairing on every accumulator.
fn outer_verify(vk: &VerifierKey, proof: &Proof, pis: Vec<Fr>) {
    let t = Instant::now();
    vk.verify(&srs().verifier, proof, pis.into_iter())
        .expect("outer verify (incl. deferred pairing)");
    println!("outer verify: {:.1?}", t.elapsed());
}

/// Where a bad inner proof got rejected.
#[derive(Debug, PartialEq, Eq)]
enum Rejection {
    /// Proving failed, because preparing the inner proof failed.
    AtPreparation,
    /// Proving succeeded, and the pairing on the accumulator failed.
    AtPairing,
}

/// Proves and verifies with a bad inner proof, and reports which step rejected
/// it. Panics if both succeed, or if either fails for another reason.
async fn expect_rejected(
    ir: &IrSource,
    pk: ProverKey<IrSource>,
    vk: &VerifierKey,
    vk_blob: &[u8],
    instance: &[Fq],
    inner_proof: Vec<u8>,
    rng: &mut ChaCha20Rng,
) -> Rejection {
    let preimage = outer_preimage(inner_proof.clone());

    let t = Instant::now();
    let (proof, pis, _skips) = match ir.prove(rng, srs(), pk, &preimage).await {
        Ok(ok) => {
            println!("outer prove: {:.1?}", t.elapsed());
            ok
        }
        Err(e) => {
            println!("rejected at prove after {:.1?} -- {e:#}", t.elapsed());
            // Preparation errors carry no context of their own, so compare
            // against preparing the inner proof directly.
            let prep = verify_proof_offcircuit(vk_blob, instance, &inner_proof, true)
                .expect_err("proving failed, so preparing the inner proof must fail too");
            assert!(
                format!("{e:#}").contains(&format!("{prep:#}")),
                "proving failed for a reason other than preparation: {e:#}"
            );
            return Rejection::AtPreparation;
        }
    };

    let t = Instant::now();
    match vk.verify(&srs().verifier, &proof, pis.into_iter()) {
        Ok(()) => panic!("the outer pipeline accepted a bad inner proof"),
        Err(e) => {
            println!("rejected at verify after {:.1?} -- {e:#}", t.elapsed());
            assert!(
                format!("{e:#}").contains("failed pairing check"),
                "verification failed for a reason other than the pairing: {e:#}"
            );
            Rejection::AtPairing
        }
    }
}
