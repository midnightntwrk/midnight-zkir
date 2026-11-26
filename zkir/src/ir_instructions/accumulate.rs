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

//! The `accumulate` instruction.
//!
//! An `Accumulator` value is always collapsed and fixed-base-resolved: one
//! point per side, with scalar one. Its pairing is left to the outer verifier,
//! once `verify_accumulator` exposes it.

use std::collections::HashSet;

use anyhow::{anyhow, bail};
use group::ff::Field;
use midnight_circuits::hash::poseidon::PoseidonChip;
use midnight_circuits::verifier::{Accumulator, AssignedAccumulator, Msm, Point};
use midnight_curves::Bls12;
use midnight_circuits::types::InnerValue;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::Error,
    poly::PolynomialLabel,
};
use midnight_zk_stdlib::ZkStdLib;
use transient_crypto::curve::outer;
use transient_crypto::proofs::DeferredAccumulator;

use crate::ir::{Identifier, Instruction as I, IrSource, Operand};
use crate::ir_types::IrType;

/// The accumulator a guarded-off instruction produces, which satisfies the
/// pairing invariant by construction.
pub fn trivial_accumulator() -> DeferredAccumulator {
    from_accumulator(&Accumulator::trivial(&[])).expect("the trivial accumulator is collapsed")
}

/// `None` unless `acc` is collapsed and fixed-base-resolved: one variable base
/// per side, with scalar one.
pub fn from_accumulator(acc: &Accumulator<Bls12>) -> Option<DeferredAccumulator> {
    let side = |msm: Msm<Bls12>| match (&msm.bases()[..], &msm.scalars()[..]) {
        ([Point::Variable(p)], [s]) if *s == outer::Scalar::ONE => Some((*p).into()),
        _ => None,
    };
    Some(DeferredAccumulator {
        lhs: side(acc.lhs())?,
        rhs: side(acc.rhs())?,
    })
}

/// Inverse of [`from_accumulator`].
pub fn to_accumulator(acc: DeferredAccumulator) -> Accumulator<Bls12> {
    let side = |p: outer::Affine| {
        Msm::new(
            &[Point::Variable(p.into())],
            &[outer::Scalar::ONE],
            &[PolynomialLabel::NoLabel],
        )
    };
    Accumulator::new(side(acc.lhs), side(acc.rhs))
}

/// Rejects `acc` unless it is collapsed and fixed-base-resolved, as it must be
/// before it is converted to public-input form.
pub fn check_collapsed(acc: &AssignedAccumulator<Bls12>) -> Result<(), Error> {
    if !acc.is_collapsed() {
        return Err(Error::Synthesis(
            "the accumulator is not collapsed and fixed-base-resolved".into(),
        ));
    }
    Ok(())
}

/// Off-circuit `accumulate`: accumulates `accs` and collapses the
/// result.
pub fn accumulate_offcircuit(accs: &[DeferredAccumulator]) -> anyhow::Result<DeferredAccumulator> {
    if accs.len() < 2 {
        bail!("`accumulate` needs at least two accumulators");
    }
    let accs: Vec<_> = accs.iter().copied().map(to_accumulator).collect();
    // The hash must match the in-circuit one, `std.poseidon_chip()`.
    let mut acc = Accumulator::accumulate::<PoseidonChip<outer::Scalar>>(&accs);
    acc.collapse();
    from_accumulator(&acc).ok_or_else(|| anyhow!("an accumulated accumulator failed to collapse"))
}

/// In-circuit counterpart of [`accumulate_offcircuit`].
pub fn accumulate_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    accs: &[AssignedAccumulator<Bls12>],
) -> Result<AssignedAccumulator<Bls12>, Error> {
    if accs.len() < 2 {
        return Err(Error::Synthesis(
            "`accumulate` needs at least two accumulators".into(),
        ));
    }
    // `accumulate` hashes the public-input form of its inputs.
    accs.iter().try_for_each(check_collapsed)?;
    let bls = std.bls12_381();
    let scalar_chip = bls.scalar_field_chip();
    let mut acc =
        AssignedAccumulator::accumulate(layouter, bls, scalar_chip, std.poseidon_chip(), accs)?;
    acc.collapse(layouter, bls, scalar_chip)?;
    Ok(acc)
}

/// The mask `randomize_accumulator` accumulates `acc` with: `acc` multiplied
/// by `factor`.
fn mask(acc: &Accumulator<Bls12>, factor: outer::Scalar) -> Accumulator<Bls12> {
    let side = |msm: Msm<Bls12>| {
        Msm::new(
            &[Point::Variable(msm.eval(&Default::default()) * factor)],
            &[outer::Scalar::ONE],
            &[PolynomialLabel::NoLabel],
        )
    };
    Accumulator::new(side(acc.lhs()), side(acc.rhs()))
}

/// Off-circuit `randomize_accumulator`.
pub fn randomize_offcircuit(
    acc: DeferredAccumulator,
    factor: outer::Scalar,
) -> anyhow::Result<DeferredAccumulator> {
    let mask = from_accumulator(&mask(&to_accumulator(acc), factor))
        .ok_or_else(|| anyhow!("a mask failed to collapse"))?;
    accumulate_offcircuit(&[mask, acc])
}

/// In-circuit counterpart of [`randomize_offcircuit`].
pub fn randomize_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    acc: &AssignedAccumulator<Bls12>,
    factor: Value<outer::Scalar>,
) -> Result<AssignedAccumulator<Bls12>, Error> {
    check_collapsed(acc)?;
    let value = acc.value().zip(factor).map(|(acc, r)| mask(&acc, r));
    let bls = std.bls12_381();
    let mask = AssignedAccumulator::assign_collapsed(
        layouter,
        bls,
        bls.scalar_field_chip(),
        &[],
        value,
    )?;
    accumulate_incircuit(std, layouter, &[mask, acc.clone()])
}

/// Tracks that each accumulator is consumed exactly once, by `accumulate` or
/// `verify_accumulator`: a dropped one is an unchecked proof.
#[derive(Default)]
struct AccumulatorUses<'a> {
    produced: HashSet<&'a Identifier>,
    /// Produced but not yet consumed, in instruction order.
    pending: Vec<&'a Identifier>,
}

impl<'a> AccumulatorUses<'a> {
    /// Records a new accumulator.
    fn produce(&mut self, id: &'a Identifier) -> anyhow::Result<()> {
        if !self.produced.insert(id) {
            bail!("accumulator {} is rebound", id.0);
        }
        self.pending.push(id);
        Ok(())
    }

    /// Records the single use of an accumulator.
    fn consume(&mut self, op: &Operand) -> anyhow::Result<()> {
        let pos = match op {
            Operand::Variable(id) => self.pending.iter().position(|p| *p == id),
            _ => None,
        }
        .ok_or_else(|| {
            anyhow!(
                "{op:?} is not an unconsumed accumulator: each one must be consumed exactly once"
            )
        })?;
        self.pending.remove(pos);
        Ok(())
    }

    /// Rejects an accumulator left unconsumed.
    fn finish(&self) -> anyhow::Result<()> {
        if let Some(id) = self.pending.first() {
            bail!(
                "accumulator {} is never verified: it must reach a `verify_accumulator`",
                id.0
            );
        }
        Ok(())
    }
}

impl I {
    /// The accumulator this instruction produces, if any.
    fn accumulator_output(&self) -> Option<&Identifier> {
        match self {
            I::PrepareVerification { output, .. }
            | I::Accumulate { output, .. }
            | I::RandomizeAccumulator { output, .. }
            | I::PrivateInput {
                val_t: IrType::Accumulator,
                output,
                ..
            }
            | I::PublicInput {
                val_t: IrType::Accumulator,
                output,
                ..
            }
            | I::LoadConstant {
                val_t: IrType::Accumulator,
                output,
                ..
            } => Some(output),
            _ => None,
        }
    }
}

impl IrSource {
    /// Number of `verify_accumulator` instructions in this circuit.
    pub fn accumulator_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|i| matches!(i, I::VerifyAccumulator { .. }))
            .count()
    }

    /// Rejects an accumulator that is dropped or used twice.
    pub(crate) fn check_accumulator_lifecycle(&self) -> anyhow::Result<()> {
        let mut accs = AccumulatorUses::default();
        // An accumulator input is unchecked, like a witnessed one.
        for input in self
            .inputs
            .iter()
            .filter(|i| matches!(i.val_t, IrType::Accumulator))
        {
            accs.produce(&input.name)?;
        }
        for ins in self.instructions.iter() {
            match ins {
                I::Accumulate { inputs, .. } => {
                    inputs.iter().try_for_each(|op| accs.consume(op))?
                }
                I::RandomizeAccumulator { input, .. } => accs.consume(input)?,
                I::VerifyAccumulator { input } => accs.consume(input)?,
                _ => {}
            }
            if let Some(output) = ins.accumulator_output() {
                accs.produce(output)?;
            }
        }
        accs.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Randomising keeps a valid accumulator valid and an invalid one invalid,
    /// and hides which accumulator it started from.
    #[test]
    fn randomizing_preserves_validity() {
        use group::{Curve, Group};
        use midnight_proofs::poly::kzg::params::ParamsKZG;
        use rand::{SeedableRng, rngs::StdRng};

        let mut rng = StdRng::seed_from_u64(0x7a);
        let params = ParamsKZG::<Bls12>::unsafe_setup(1, &mut rng);
        let verifier = params.verifier_params();
        // Over the domain {1, -1}: `G = L_0 + L_1` and `tau G = L_0 - L_1`.
        let [l0, l1] = [params.g_lagrange()[0], params.g_lagrange()[1]].map(midnight_curves::G1Projective::from);
        let (g, tau_g) = ((l0 + l1).to_affine(), (l0 - l1).to_affine());
        let check = |acc: DeferredAccumulator| {
            to_accumulator(acc).check(&verifier, &Default::default())
        };
        let valid = [
            DeferredAccumulator { lhs: g, rhs: tau_g },
            DeferredAccumulator { lhs: tau_g, rhs: g },
        ]
        .into_iter()
        .find(|acc| check(*acc))
        .expect("one orientation of (G, tau G) pairs");
        let invalid = DeferredAccumulator {
            lhs: valid.lhs,
            rhs: (midnight_curves::G1Projective::from(valid.rhs) + midnight_curves::G1Projective::generator()).to_affine(),
        };
        assert!(!check(invalid));

        for factor in [outer::Scalar::from(3u64), outer::Scalar::from(0u64)] {
            let randomized = randomize_offcircuit(valid, factor).unwrap();
            assert!(check(randomized));
            assert_ne!(randomized, valid);
            assert!(!check(randomize_offcircuit(invalid, factor).unwrap()));
        }
        assert_ne!(
            randomize_offcircuit(valid, outer::Scalar::from(3u64)).unwrap(),
            randomize_offcircuit(valid, outer::Scalar::from(4u64)).unwrap()
        );
    }

    #[test]
    fn accumulation_needs_two_accumulators() {
        let acc = accumulate_offcircuit(&[trivial_accumulator(), trivial_accumulator()]).unwrap();
        assert_eq!(acc, trivial_accumulator());
        assert!(accumulate_offcircuit(&[acc]).is_err());
    }
}
