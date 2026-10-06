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
use midnight_circuits::verifier::{Accumulator, AssignedAccumulator};
use midnight_proofs::{circuit::Layouter, plonk::Error};
use midnight_zk_stdlib::ZkStdLib;
use transient_crypto::curve::outer;
use transient_crypto::proofs::{DeferredAccumulator, InnerSelfEmulation as S};

use crate::ir::{Identifier, Instruction as I, IrSource, Operand};
use crate::ir_types::IrType;

/// The accumulator a guarded-off instruction produces, which satisfies the
/// pairing invariant by construction.
pub fn trivial_accumulator() -> DeferredAccumulator {
    DeferredAccumulator::new(&Accumulator::<S>::trivial(&[]))
        .expect("the trivial accumulator is collapsed")
}

/// Rejects `acc` unless it is collapsed and fixed-base-resolved, as it must be
/// before it is converted to public-input form.
pub fn check_collapsed(acc: &AssignedAccumulator<S>) -> Result<(), Error> {
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
    let accs: Vec<_> = accs.iter().map(|acc| acc.to_accumulator()).collect();
    let mut acc = Accumulator::accumulate(&accs);
    acc.collapse();
    DeferredAccumulator::new(&acc)
        .ok_or_else(|| anyhow!("an accumulated accumulator failed to collapse"))
}

/// In-circuit counterpart of [`accumulate_offcircuit`].
pub fn accumulate_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    accs: &[AssignedAccumulator<S>],
) -> Result<AssignedAccumulator<S>, Error> {
    if accs.len() < 2 {
        return Err(Error::Synthesis(
            "`accumulate` needs at least two accumulators".into(),
        ));
    }
    // `accumulate` hashes the public-input form of its inputs.
    accs.iter().try_for_each(check_collapsed)?;
    let bls = std.bls12_381();
    // TODO: if we use truncated challenges it may make sense to collapse before
    // accumulating.
    let mut acc = std.verifier().accumulate(layouter, accs)?;
    acc.collapse(layouter, bls, bls.scalar_field_chip())?;
    Ok(acc)
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
    fn produce(&mut self, id: &'a Identifier) -> anyhow::Result<()> {
        if !self.produced.insert(id) {
            bail!("accumulator {} is rebound", id.0);
        }
        self.pending.push(id);
        Ok(())
    }

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

impl IrSource {
    /// Number of `verify_accumulator` instructions in this circuit.
    pub fn accumulator_count(&self) -> usize {
        self.instructions
            .iter()
            .filter(|i| matches!(i, I::VerifyAccumulator { .. }))
            .count()
    }

    /// Rejects an accumulator that is dropped or used twice.
    pub(crate) fn validate_accumulators(&self) -> anyhow::Result<()> {
        let mut accs = AccumulatorUses::default();
        for ins in self.instructions.iter() {
            match ins {
                I::VerifyProof { output, .. }
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
                } => accs.produce(output)?,
                I::Accumulate { inputs, output } => {
                    inputs.iter().try_for_each(|op| accs.consume(op))?;
                    accs.produce(output)?;
                }
                I::VerifyAccumulator { input } => accs.consume(input)?,
                _ => {}
            }
        }
        accs.finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accumulation_needs_two_accumulators() {
        let acc = accumulate_offcircuit(&[trivial_accumulator(), trivial_accumulator()]).unwrap();
        assert_eq!(acc, trivial_accumulator());
        assert!(accumulate_offcircuit(&[acc]).is_err());
    }
}
