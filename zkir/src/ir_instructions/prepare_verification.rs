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

//! The `prepare_verification` instruction: partially verify an inner Midnight proof,
//! producing the (deferred) accumulator it leaves for the final pairing. Built
//! directly on the verifier-gadget primitives that midnight-circuits exposes.
//! The accumulator is only checked once a `verify_accumulator` exposes it; the
//! verifier side (reconstructing each accumulator from the public inputs and
//! running its pairing check) lives in `transient-crypto`.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

use anyhow::{anyhow, bail};
use group::Group;
use midnight_circuits::hash::poseidon::PoseidonState;
use midnight_circuits::instructions::AssignmentInstructions;
use midnight_circuits::types::{AssignedBit, AssignedNative};
use midnight_circuits::verifier::{
    Accumulator, AssignedAccumulator, AssignedVk, InCircuitTranscript, fixed_bases,
};
use midnight_curves::{Bls12, G1Projective};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{self, Error},
    poly::PolynomialLabel,
    transcript::{CircuitTranscript, Transcript},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{KZG, MidnightVK, ZkStdLib};
use transient_crypto::curve::{Fr, outer};
use transient_crypto::proofs::DeferredAccumulator;

use crate::ir::{Identifier, Instruction as I, IrSource, Operand};
use crate::ir_instructions::accumulate::{from_accumulator, trivial_accumulator};
use crate::ir_instructions::unbound_vk::{InnerVerifyingKey, fixed_vk_info};
use crate::ir_types::{AssignedBoundKey, BoundKey, CircuitValue, InnerVk, IrType, IrValue};

/// Off-circuit half of `prepare_verification` on a fixed key: partially
/// verifies the inner proof and returns the accumulator the check defers,
/// resolved and collapsed.
///
/// If `guard` is `false` neither key nor proof is read and the trivial
/// accumulator is returned.
pub fn prepare_verification_offcircuit(
    vk_blob: &[u8],
    instance: &[outer::Scalar],
    proof: &[u8],
    guard: bool,
) -> anyhow::Result<DeferredAccumulator> {
    if !guard {
        return Ok(trivial_accumulator());
    }
    let IrValue::BoundVk(key) = load_constant_vk_offcircuit(vk_blob)? else {
        unreachable!("a constant key loads as a BoundVk");
    };
    prepare_verification_key_offcircuit(&key, instance, proof, guard)
}

pub fn prepare_verification_key_offcircuit(
    key: &BoundKey,
    instance: &[outer::Scalar],
    proof: &[u8],
    guard: bool,
) -> anyhow::Result<DeferredAccumulator> {
    if !guard {
        return Ok(trivial_accumulator());
    }
    let bases = if key.constant {
        fixed_bases::<Bls12, KZG>(&key.vk.0)
    } else {
        bound_bases()
    };
    prepare_offcircuit(&key.vk.0, &bases, instance, proof)
}

pub fn load_constant_vk_offcircuit(vk_blob: &[u8]) -> anyhow::Result<IrValue> {
    let vk = MidnightVK::<KZG>::read(&mut &vk_blob[..], SerdeFormat::Processed)
        .map_err(|e| anyhow!("reading inner verifying key: {e}"))?;
    Ok(IrValue::BoundVk(BoundKey {
        vk: InnerVk(Arc::new(vk.vk().clone())),
        constant: true,
    }))
}

pub fn load_constant_vk_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    vk_blob: &[u8],
) -> Result<CircuitValue, Error> {
    let vk = MidnightVK::<KZG>::read(&mut &vk_blob[..], SerdeFormat::Processed)
        .map_err(|e| Error::Synthesis(format!("inner verifying key: {e}")))?;
    let plonk_vk = vk.vk();

    // Only `transcript_repr` enters the transcript, but it cannot disagree
    // with the key: `MidnightVK::read` never reads it, `VerifyingKey::from_parts`
    // recomputes it from the commitments, domain and cs parsed here, the same
    // ones the fixed bases below are taken from.
    let assigned_vk = std.verifier::<KZG>().assign_fixed_vk(
        layouter,
        plonk_vk.get_domain(),
        plonk_vk.cs(),
        plonk_vk.transcript_repr(),
    )?;
    Ok(CircuitValue::BoundVk(AssignedBoundKey {
        vk: assigned_vk,
        bases: fixed_bases::<Bls12, KZG>(plonk_vk),
    }))
}

/// The bases of a bound key's accumulator that are circuit constants: only the
/// negated generator the KZG opening introduces, the key's own commitments
/// being witnessed.
pub(crate) fn bound_bases() -> BTreeMap<PolynomialLabel, G1Projective> {
    BTreeMap::from([(
        PolynomialLabel::Custom("-G".into()),
        -G1Projective::generator(),
    )])
}

/// Partially verifies `proof` under `plonk_vk`, and resolves `bases` in the
/// accumulator it leaves.
fn prepare_offcircuit(
    plonk_vk: &InnerVerifyingKey,
    bases: &BTreeMap<PolynomialLabel, G1Projective>,
    instance: &[outer::Scalar],
    proof: &[u8],
) -> anyhow::Result<DeferredAccumulator> {
    let mut transcript = CircuitTranscript::<PoseidonState<outer::Scalar>>::init_from_bytes(proof);
    let dual_msm =
        plonk::prepare::<outer::Scalar, KZG, CircuitTranscript<PoseidonState<outer::Scalar>>>(
            plonk_vk,
            // No committed instance, so its column is an empty instance
            // column, as `midnight_zk_stdlib::verify` lays it out.
            &[],
            &[&[], instance],
            &mut transcript,
        )?;

    let mut acc = Accumulator::from_dual_msm(dual_msm, bases);
    acc.resolve_fixed_bases(bases);
    acc.collapse();

    from_accumulator(&acc)
        .ok_or_else(|| anyhow!("the inner proof's accumulator failed to collapse"))
}

/// In-circuit half of [`prepare_verification_offcircuit`]: verifies the inner proof and
/// returns its accumulator, resolved and collapsed.
///
/// If `guard` is `0` the accumulator is reduced to the trivial one, so the
/// deferred pairing holds whatever the prover supplied.
pub fn prepare_verification_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    vk_blob: &[u8],
    instance: &[AssignedNative<outer::Scalar>],
    proof: Value<Vec<u8>>,
    guard: &AssignedBit<outer::Scalar>,
) -> Result<AssignedAccumulator<Bls12>, Error> {
    let CircuitValue::BoundVk(key) = load_constant_vk_incircuit(std, layouter, vk_blob)? else {
        unreachable!("a constant key loads as a BoundVk");
    };
    prepare_verification_key_incircuit(std, layouter, &key, instance, proof, guard)
}

pub fn prepare_verification_key_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    key: &AssignedBoundKey,
    instance: &[AssignedNative<outer::Scalar>],
    proof: Value<Vec<u8>>,
    guard: &AssignedBit<outer::Scalar>,
) -> Result<AssignedAccumulator<Bls12>, Error> {
    prepare_incircuit(std, layouter, &key.vk, &key.bases, instance, proof, guard)
}

/// Verifies `proof` under `assigned_vk` in-circuit, resolving `bases` in the
/// accumulator it leaves, which is trivial if `guard` is `0`.
fn prepare_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    assigned_vk: &AssignedVk<outer::Scalar, KZG>,
    bases: &BTreeMap<PolynomialLabel, G1Projective>,
    instance: &[AssignedNative<outer::Scalar>],
    proof: Value<Vec<u8>>,
    guard: &AssignedBit<outer::Scalar>,
) -> Result<AssignedAccumulator<Bls12>, Error> {
    let verifier = std.verifier::<KZG>();
    let bls = std.bls12_381();
    let scalar_chip = bls.scalar_field_chip();

    // Assign the constant bases in-circuit, keyed by the same labels as
    // off-circuit.
    let mut assigned_bases = BTreeMap::new();
    for (label, base) in bases {
        assigned_bases.insert(label.clone(), bls.assign_fixed(layouter, *base)?);
    }

    // No committed instance, mirroring the off-circuit `prepare`.
    let mut transcript = std.verifier_transcript();
    transcript.init_with_proof(layouter, proof)?;
    let mut acc = verifier.prepare(
        layouter,
        assigned_vk,
        &[],
        &[&[], instance],
        &mut transcript,
    )?;
    acc.resolve_fixed_bases(&assigned_bases);
    AssignedAccumulator::scale_by_bit(layouter, scalar_chip, guard, &mut acc)?;
    acc.collapse(layouter, bls, scalar_chip)?;
    Ok(acc)
}

/// Tracks that each `inner_proof` binding is used by exactly one
/// `prepare_verification`, under the same guard.
///
/// Guards must match because each instruction reads only its own: guarded
/// off, `inner_proof` binds an empty blob that a `prepare_verification` guarded on
/// would then fail to verify.
#[derive(Default)]
struct InnerProofUses<'a> {
    bound: HashSet<&'a Identifier>,
    /// Bound but not yet verified, with their guard, in instruction order.
    pending: Vec<(&'a Identifier, &'a Operand)>,
}

impl<'a> InnerProofUses<'a> {
    /// Records an `inner_proof` binding.
    fn bind(&mut self, id: &'a Identifier, guard: &'a Operand) -> anyhow::Result<()> {
        if !self.bound.insert(id) {
            bail!("`inner_proof` rebinds {}", id.0);
        }
        self.pending.push((id, guard));
        Ok(())
    }

    /// Records the `prepare_verification` of a bound proof.
    fn verify(&mut self, proof: &Identifier, guard: &Operand) -> anyhow::Result<()> {
        let Some(pos) = self.pending.iter().position(|(id, _)| *id == proof) else {
            if self.bound.contains(proof) {
                bail!("{} is verified more than once", proof.0);
            }
            bail!(
                "`prepare_verification` names {}, which no preceding `inner_proof` binds",
                proof.0
            );
        };
        let (_, bound_guard) = self.pending.remove(pos);
        if bound_guard != guard {
            bail!(
                "`prepare_verification` on {} is guarded differently to the `inner_proof` that bound it",
                proof.0
            );
        }
        Ok(())
    }

    /// Rejects a bound proof left unverified.
    fn finish(&self) -> anyhow::Result<()> {
        if let Some((id, _)) = self.pending.first() {
            bail!(
                "`inner_proof` binds {}, which no `prepare_verification` uses",
                id.0
            );
        }
        Ok(())
    }
}

impl IrSource {
    /// Rejects a malformed `inner_proof` / `prepare_verification` pair: each
    /// `prepare_verification` must name a proof an earlier `inner_proof` bound, under
    /// the same guard, and each bound proof must be used exactly once.
    pub(crate) fn validate_inner_proofs(&self) -> anyhow::Result<()> {
        let mut proofs = InnerProofUses::default();
        for ins in self.instructions.iter() {
            match ins {
                I::InnerProof { guard, output } => proofs.bind(output, guard)?,
                I::PrepareVerification { guard, proof, .. } => proofs.verify(proof, guard)?,
                _ => {}
            }
        }
        proofs.finish()
    }

    /// Indexes [`IrSource::inner_vks`] by `vk_id`, so each `LoadConstant` of a
    /// `BoundVk` can resolve its key.
    ///
    /// Rejects a duplicated key, and one left unused by every instruction, so
    /// the side-table stays a canonical set of the keys the circuit needs.
    pub(crate) fn resolve_inner_vks(&self) -> anyhow::Result<HashMap<Vec<u8>, ConstantVk<'_>>> {
        let mut vk_map: HashMap<Vec<u8>, ConstantVk<'_>> = HashMap::new();
        for vk_blob in self.inner_vks.iter() {
            let (vk_id, nb_public_inputs) = fixed_vk_info(vk_blob)?;
            let entry = ConstantVk {
                blob: vk_blob,
                nb_public_inputs,
            };
            if vk_map.insert(vk_id.as_le_bytes(), entry).is_some() {
                bail!("duplicate verifying key in `inner_vks`");
            }
        }

        let mut used = HashSet::new();
        for ins in self.instructions.iter() {
            if let I::LoadConstant {
                val_t: IrType::BoundVk,
                encoding,
                ..
            } = ins
            {
                let vk_id = constant_vk_name(encoding)?;
                if !vk_map.contains_key(&vk_id) {
                    bail!(
                        "no verifying key in `inner_vks` for vk_id {}",
                        serde_json::to_string(&Operand::Immediate(encoding[0])).unwrap_or_default()
                    );
                }
                used.insert(vk_id);
            }
        }

        if used.len() != vk_map.len() {
            bail!(
                "`inner_vks` holds {} keys but only {} are used",
                vk_map.len(),
                used.len()
            );
        }
        Ok(vk_map)
    }
}

#[derive(Clone, Copy)]
pub(crate) struct ConstantVk<'a> {
    pub blob: &'a [u8],
    pub nb_public_inputs: usize,
}

pub(crate) fn constant_vk_name(encoding: &[Fr]) -> anyhow::Result<Vec<u8>> {
    match encoding {
        [vk_id] => Ok(vk_id.as_le_bytes()),
        _ => bail!(
            "a constant BoundVk is encoded as its vk_id alone, got {} field elements",
            encoding.len()
        ),
    }
}
