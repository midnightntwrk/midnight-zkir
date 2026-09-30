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

//! The `aggregate_accumulators` instruction.
//!
//! An `Accumulator` value is always collapsed and fixed-base-resolved: one
//! point per side, with scalar one. Its pairing is left to the outer verifier,
//! once `verify_accumulator` exposes it.

use anyhow::{anyhow, bail};
use midnight_circuits::verifier::{Accumulator, AssignedAccumulator};
use midnight_proofs::{circuit::Layouter, plonk::Error};
use midnight_zk_stdlib::ZkStdLib;
use transient_crypto::curve::outer;
use transient_crypto::proofs::{DeferredAccumulator, InnerSelfEmulation as S};

/// The accumulator a guarded-off instruction produces, which satisfies the
/// pairing invariant by construction.
pub fn trivial_accumulator() -> DeferredAccumulator {
    DeferredAccumulator::from_accumulator(&Accumulator::<S>::trivial(&[]))
        .expect("the trivial accumulator is collapsed")
}

/// Off-circuit `aggregate_accumulators`: accumulates `accs` and collapses the
/// result.
pub fn aggregate_offcircuit(accs: &[DeferredAccumulator]) -> anyhow::Result<DeferredAccumulator> {
    if accs.len() < 2 {
        bail!("`aggregate_accumulators` needs at least two accumulators");
    }
    let accs: Vec<_> = accs.iter().map(|acc| acc.to_accumulator()).collect();
    let mut acc = Accumulator::accumulate(&accs);
    acc.collapse();
    DeferredAccumulator::from_accumulator(&acc)
        .ok_or_else(|| anyhow!("an aggregated accumulator failed to collapse"))
}

/// In-circuit counterpart of [`aggregate_offcircuit`].
pub fn aggregate_incircuit(
    std: &ZkStdLib,
    layouter: &mut impl Layouter<outer::Scalar>,
    accs: &[AssignedAccumulator<S>],
) -> Result<AssignedAccumulator<S>, Error> {
    if accs.len() < 2 {
        return Err(Error::Synthesis(
            "`aggregate_accumulators` needs at least two accumulators".into(),
        ));
    }
    let bls = std.bls12_381();
    // TODO: if we use truncated challenges it may make sense to collapse before
    // accumulating.
    let mut acc = std.verifier().accumulate(layouter, accs)?;
    acc.collapse(layouter, bls, bls.scalar_field_chip())?;
    Ok(acc)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn aggregation_needs_two_accumulators() {
        let acc = aggregate_offcircuit(&[trivial_accumulator(), trivial_accumulator()]).unwrap();
        assert_eq!(acc, trivial_accumulator());
        assert!(aggregate_offcircuit(&[acc]).is_err());
    }
}
