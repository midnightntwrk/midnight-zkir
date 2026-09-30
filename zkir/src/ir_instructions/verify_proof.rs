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

//! The `verify_proof` instruction: partially verify an inner Midnight proof,
//! producing the (deferred) accumulator it leaves for the final pairing. Built
//! directly on the verifier-gadget primitives that midnight-circuits exposes.
//! The accumulator is only checked once a `verify_accumulator` exposes it; the
//! verifier side (reconstructing each accumulator from the public inputs and
//! running its pairing check) lives in `transient-crypto`.

use std::collections::BTreeMap;

use anyhow::anyhow;
use group::Group;
use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_circuits::instructions::AssignmentInstructions;
use midnight_circuits::types::{AssignedBit, AssignedNative};
use midnight_circuits::verifier::{Accumulator, AssignedAccumulator, SelfEmulation, fixed_bases};
use midnight_curves::Bls12;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, Error},
    poly::kzg::KZGCommitmentScheme,
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{MidnightVK, ZkStdLib};
use sha2::{Digest, Sha256};
use transient_crypto::curve::outer;
use transient_crypto::proofs::{DeferredAccumulator, InnerSelfEmulation as S};

use crate::ir_instructions::aggregate::trivial_accumulator;

/// Label prefix for an inner verifying key's fixed bases.
///
/// Derived from the blob's own digest.
fn vk_name(vk_blob: &[u8]) -> String {
    format!("inner_vk_{}", const_hex::encode(Sha256::digest(vk_blob)))
}

/// Off-circuit half of `verify_proof`: partially verifies the inner proof and
/// returns the accumulator the check defers, resolved and collapsed.
///
/// If `guard` is `false` neither key nor proof is read and the trivial
/// accumulator is returned.
pub fn verify_proof_offcircuit(
    vk_blob: &[u8],
    instance: &[outer::Scalar],
    proof: &[u8],
    guard: bool,
) -> anyhow::Result<DeferredAccumulator> {
    if !guard {
        return Ok(trivial_accumulator());
    }

    let vk = MidnightVK::read(&mut &vk_blob[..], SerdeFormat::Processed)
        .map_err(|e| anyhow!("reading inner verifying key: {e}"))?;
    let plonk_vk = vk.vk();
    let vk_name = vk_name(vk_blob);
    let bases = fixed_bases::<S>(&vk_name, plonk_vk);

    let mut transcript = CircuitTranscript::<PoseidonState<outer::Scalar>>::init_from_bytes(proof);
    let dual_msm = plonk::prepare::<
        outer::Scalar,
        KZGCommitmentScheme<Bls12>,
        CircuitTranscript<PoseidonState<outer::Scalar>>,
    >(
        plonk_vk,
        &[&[<S as SelfEmulation>::C::identity()]],
        &[&[instance]],
        &mut transcript,
    )?;

    let mut acc = Accumulator::<S>::from_dual_msm(dual_msm, &vk_name, &bases);
    acc.resolve_fixed_bases(&bases);
    acc.collapse();

    DeferredAccumulator::from_accumulator(&acc)
        .ok_or_else(|| anyhow!("the inner proof's accumulator failed to collapse"))
}

/// In-circuit half of [`verify_proof_offcircuit`]: verifies the inner proof and
/// returns its accumulator, resolved and collapsed.
///
/// If `guard` is `0` the accumulator is reduced to the trivial one, so the
/// deferred pairing holds whatever the prover supplied.
pub fn verify_proof_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    vk_blob: &[u8],
    instance: &[&[AssignedNative<outer::Scalar>]],
    proof: Value<Vec<u8>>,
    guard: &AssignedBit<outer::Scalar>,
) -> Result<AssignedAccumulator<S>, Error> {
    let vk = MidnightVK::read(&mut &vk_blob[..], SerdeFormat::Processed)
        .map_err(|e| Error::Synthesis(format!("inner verifying key: {e}")))?;
    let plonk_vk = vk.vk();
    let vk_name = vk_name(vk_blob);
    let verifier = std.verifier();
    let bls = std.bls12_381();
    let scalar_chip = bls.scalar_field_chip();

    // Exactly one instance set, matching the off-circuit `&[&[instance]]`.
    if instance.len() != 1 {
        return Err(Error::Synthesis(
            "`verify_proof` supports exactly one instance set".into(),
        ));
    }

    let assigned_vk = verifier.assign_fixed_vk(
        layouter,
        &vk_name,
        plonk_vk.get_domain(),
        plonk_vk.cs(),
        plonk_vk.transcript_repr(),
    )?;

    // Assign the inner VK's fixed bases in-circuit, keyed by the same names
    // `fixed_bases` produces.
    let mut assigned_bases = BTreeMap::new();
    for (name, base) in fixed_bases::<S>(&vk_name, plonk_vk) {
        assigned_bases.insert(name, bls.assign_fixed(layouter, base)?);
    }

    // The committed instance is a single identity point (we do not support
    // committed instances), mirroring the off-circuit `&[&[C::identity()]]`.
    let committed = [bls.assign_fixed(layouter, <S as SelfEmulation>::C::identity())?];

    let mut acc = verifier.prepare(layouter, &assigned_vk, &committed, instance, proof)?;
    acc.resolve_fixed_bases(&assigned_bases);
    AssignedAccumulator::scale_by_bit(layouter, scalar_chip, guard, &mut acc)?;
    acc.collapse(layouter, bls, scalar_chip)?;
    Ok(acc)
}
