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

//! Verifying keys of inner proofs, witnessed privately (`AssignUnboundVk`) and
//! bound to their `vk_id` (`BindVk`), and the `vk_id` that names every inner
//! key, fixed or private.

use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex, OnceLock};

use anyhow::{anyhow, bail};
use group::{Group, GroupEncoding};
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    instructions::{
        AssertionInstructions, AssignmentInstructions, ControlFlowInstructions, hash::HashCPU,
    },
    types::{AssignedBit, AssignedNative},
    verifier::{AssignedVk, UnboundVk, vk_hash},
};
use midnight_curves::G1Projective;
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, VerifyingKey},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{KZG, MidnightVK, ZkStdLib, ZkStdLibArch};
use transient_crypto::curve::Fr;

use crate::{
    ir::{Identifier, Instruction as I, IrSource, Operand, VkRef},
    ir_instructions::F,
    ir_types::{CircuitValue, InnerVk, IrValue},
};

/// The verifying key of an inner proof, as handed to zkir.
pub type InnerVerifyingKey = VerifyingKey<F, KZG>;

/// Architecture of the inner circuits whose keys `AssignUnboundVk` witnesses:
/// every chip of the standard library is enabled.
pub const INNER_ARCH: ZkStdLibArch = ZkStdLibArch {
    jubjub: true,
    poseidon: true,
    sha2_256: true,
    sha2_512: true,
    sha3_256: true,
    keccak_256: true,
    blake2b: true,
    secp256k1: true,
    p256: true,
    bls12_381: true,
    curve25519: true,
    base64: true,
    automaton: true,
    nb_arith_cols: 5,
    nr_pow2range_cols: 4,
};

/// Domain separator of [`vk_id`]: `"midnight-zkir:vk_id:v1"`, read as a
/// little-endian integer.
const VK_ID_TAG: &[u8] = b"midnight-zkir:vk_id:v1";

fn vk_id_tag() -> F {
    Fr::from_le_bytes(VK_ID_TAG)
        .expect("the vk_id tag fits in a field element")
        .0
}

/// The identity of an inner verifying key, with `nb_public_inputs` public
/// inputs: `Poseidon(tag, nb_public_inputs, vk_hash(vk))`, where `vk_hash` is
/// midnight-zk's hash of the key and `tag` separates it from other Poseidon
/// values.
///
/// `vk_hash` covers the key's `transcript_repr`, so this tracks its definition
/// in midnight-proofs: a change there changes every key's identity.
pub fn vk_id(vk: &InnerVerifyingKey, nb_public_inputs: usize) -> Fr {
    let raw = vk_hash::<PoseidonChip<F>, F, KZG>(vk);
    Fr(<PoseidonChip<F> as HashCPU<F, F>>::hash(&[
        vk_id_tag(),
        F::from(nb_public_inputs as u64),
        raw,
    ]))
}

/// The `vk_id` of a fixed key, serialized as `MidnightVK::write(Processed)`
/// outputs it.
pub fn fixed_vk_id(blob: &[u8]) -> anyhow::Result<Fr> {
    let vk = MidnightVK::<KZG>::read(&mut &blob[..], SerdeFormat::Processed)
        .map_err(|e| anyhow!("reading verifying key in `inner_vks`: {e}"))?;
    // `MidnightVK` does not expose its number of public inputs: it is the
    // `u32` written just before the inner key, which ends the blob.
    let end = blob.len() - vk.vk().bytes_length(SerdeFormat::Processed);
    let nb_public_inputs = u32::from_le_bytes(
        blob[end - 4..end]
            .try_into()
            .expect("the slice is 4 bytes long"),
    );
    Ok(vk_id(vk.vk(), nb_public_inputs as usize))
}

/// The constraint system of an inner circuit of size `2^k`, as configured when
/// reading its `MidnightVK`.
fn inner_cs(k: u8) -> anyhow::Result<ConstraintSystem<F>> {
    let max_bit_len = k
        .checked_sub(1)
        .ok_or_else(|| anyhow!("`assign_unbound_vk`: k must be positive"))?;
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (INNER_ARCH, max_bit_len));
    Ok(cs)
}

/// A representation of a constraint system that tells them apart, as
/// midnight-proofs hashes it into `transcript_repr`.
fn pinned_cs(cs: &ConstraintSystem<F>) -> String {
    format!("{:?}", cs.pinned())
}

/// A finalized constraint system, with its pinned representation.
type PinnedCs = Arc<(ConstraintSystem<F>, String)>;

/// The finalized `INNER_ARCH` constraint system of size `2^k`, with its
/// pinned representation, cached by `k`.
fn finalized_inner_cs(k: u8) -> anyhow::Result<PinnedCs> {
    static CACHE: OnceLock<Mutex<HashMap<u8, PinnedCs>>> = OnceLock::new();
    let mut cache = CACHE
        .get_or_init(Default::default)
        .lock()
        .expect("cs cache");
    if let Some(cs) = cache.get(&k) {
        return Ok(cs.clone());
    }
    let cs = inner_cs(k)?.into_finalized();
    let pinned = pinned_cs(&cs);
    let entry = Arc::new((cs, pinned));
    cache.insert(k, entry.clone());
    Ok(entry)
}

/// Rejects a key that is not of size `2^k` and of the `INNER_ARCH` shape.
fn check_inner_vk(vk: &InnerVerifyingKey, k: u8) -> anyhow::Result<()> {
    let size = vk.get_domain().k();
    if size != u32::from(k) {
        bail!("`assign_unbound_vk`: expected a key of size 2^{k}, got one of size 2^{size}");
    }
    if pinned_cs(vk.cs()) != finalized_inner_cs(k)?.1 {
        bail!(
            "`assign_unbound_vk`: the key's constraint system is not the one of an inner circuit of size 2^{k} with every chip enabled"
        );
    }
    Ok(())
}

/// A key of the `INNER_ARCH` shape and of size `2^k`, which zkir witnesses
/// where `AssignUnboundVk` is guarded off. Its commitments are all the
/// generator: it is a valid key in every respect the circuit checks, but
/// verifies no proof.
fn dummy_vk(k: u8) -> anyhow::Result<Arc<InnerVerifyingKey>> {
    static CACHE: OnceLock<Mutex<HashMap<u8, Arc<InnerVerifyingKey>>>> = OnceLock::new();
    let mut cache = CACHE
        .get_or_init(Default::default)
        .lock()
        .expect("dummy cache");
    if let Some(vk) = cache.get(&k) {
        return Ok(vk.clone());
    }

    // The `VerifyingKey::write` layout: its version, `k`, then one commitment
    // per fixed polynomial.
    const VK_VERSION: u8 = 0x03;
    let nb_commitments = finalized_inner_cs(k)?.0.fixed_polys_labels().len();
    let generator = G1Projective::generator().to_bytes();
    let mut bytes = vec![VK_VERSION, k];
    for _ in 0..nb_commitments {
        bytes.extend_from_slice(generator.as_ref());
    }
    let vk = VerifyingKey::read_from_cs(&mut &bytes[..], SerdeFormat::Processed, inner_cs(k)?)
        .map_err(|e| anyhow!("building the dummy key of size 2^{k}: {e}"))?;

    let vk = Arc::new(vk);
    cache.insert(k, vk.clone());
    Ok(vk)
}

/// Off-circuit half of `assign_unbound_vk`: the key supplied for this slot,
/// checked, or a dummy key if `guard` is `false`.
pub fn assign_unbound_vk_offcircuit(
    supplied: Option<&InnerVerifyingKey>,
    slot: usize,
    k: u8,
    guard: bool,
) -> anyhow::Result<IrValue> {
    let vk = if guard {
        let vk = supplied.ok_or_else(|| {
            anyhow!("no verifying key supplied for `assign_unbound_vk` slot {slot}")
        })?;
        check_inner_vk(vk, k)?;
        Arc::new(vk.clone())
    } else {
        dummy_vk(k)?
    };
    Ok(IrValue::UnboundVk(InnerVk(vk)))
}

/// Witnesses the verifying key of an inner circuit of size `2^k`.
pub fn assign_unbound_vk_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    k: u8,
    value: Value<IrValue>,
) -> Result<CircuitValue, Error> {
    let vk = value
        .map_with_result(|v| InnerVk::try_from(v).map_err(|e| Error::Synthesis(e.to_string())))?;
    let cs = finalized_inner_cs(k).map_err(|e| Error::Synthesis(e.to_string()))?;
    std_lib
        .verifier::<KZG>()
        .assign_unbound_vk(layouter, vk.as_ref().map(|vk| vk.0.as_ref()), &cs.0)
        .map(CircuitValue::UnboundVk)
}

/// Off-circuit half of `bind_vk`: checks that `vk` has `vk_id` `hash`, if
/// `guard` is `true`, and returns it bound.
pub fn bind_vk_offcircuit(
    vk: IrValue,
    hash: IrValue,
    nb_public_inputs: usize,
    guard: bool,
) -> anyhow::Result<IrValue> {
    let vk: InnerVk = vk.try_into()?;
    let hash: Fr = hash.try_into()?;
    if guard && vk_id(&vk.0, nb_public_inputs) != hash {
        bail!("`bind_vk`: the verifying key does not match the given hash");
    }
    Ok(IrValue::BoundVk(vk))
}

/// In-circuit half of `bind_vk`: constrains `vk` to have `vk_id` `hash`, if
/// `guard` is `1`. `value` is the key's off-circuit value.
pub fn bind_vk_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    vk: CircuitValue,
    value: Value<IrValue>,
    hash: CircuitValue,
    nb_public_inputs: usize,
    guard: &AssignedBit<F>,
) -> Result<CircuitValue, Error> {
    let vk: UnboundVk<F, KZG> = vk.try_into()?;
    let hash: AssignedNative<F> = hash.try_into()?;

    // midnight-zk binds the key to its raw `vk_hash`, which `vk_id` then wraps.
    let raw = value.map_with_result(|v| {
        InnerVk::try_from(v)
            .map(|vk| vk_hash::<PoseidonChip<F>, F, KZG>(&vk.0))
            .map_err(|e| Error::Synthesis(e.to_string()))
    })?;
    let raw: AssignedNative<F> = std_lib.assign(layouter, raw)?;
    let vk: AssignedVk<F, KZG> =
        std_lib
            .verifier::<KZG>()
            .bind_vk_to_hash(layouter, std_lib.poseidon_chip(), vk, &raw)?;

    let tag: AssignedNative<F> = std_lib.assign_fixed(layouter, vk_id_tag())?;
    let nb: AssignedNative<F> = std_lib.assign_fixed(layouter, F::from(nb_public_inputs as u64))?;
    let id = std_lib.poseidon(layouter, &[tag, nb, raw])?;

    // Guarded off, the key is compared to its own `vk_id`.
    let expected = std_lib.select(layouter, guard, &hash, &id)?;
    std_lib.assert_equal(layouter, &id, &expected)?;
    Ok(CircuitValue::BoundVk(vk))
}

/// Where a private key comes from, as [`IrSource::validate_private_vks`]
/// traces it.
#[derive(Clone)]
pub(crate) struct PrivateVkInfo<'a> {
    pub guard: &'a Operand,
    pub nb_public_inputs: usize,
}

/// The keys of a circuit's `AssignUnboundVk` and `BindVk` outputs.
#[derive(Default)]
pub(crate) struct PrivateVks<'a> {
    pub unbound: HashMap<&'a Identifier, PrivateVkInfo<'a>>,
    pub bound: HashMap<&'a Identifier, PrivateVkInfo<'a>>,
}

impl<'a> PrivateVks<'a> {
    /// The number of public inputs the key `vk` declares, if `vk` is the
    /// output of an `AssignUnboundVk`.
    pub fn unbound_nb_public_inputs(&self, vk: &Operand) -> anyhow::Result<usize> {
        match vk {
            Operand::Variable(id) => self.unbound.get(id).map(|info| info.nb_public_inputs),
            Operand::Immediate(_) => None,
        }
        .ok_or_else(|| anyhow!("`bind_vk` takes an UnboundVk produced by `assign_unbound_vk`"))
    }
}

impl IrSource {
    /// The number of keys [`IrSource::check_with_inner_vks`] and
    /// [`IrSource::prove_with_inner_vks`] take: one per `AssignUnboundVk`.
    pub fn inner_vk_slots(&self) -> usize {
        self.instructions
            .iter()
            .filter(|i| matches!(i, I::AssignUnboundVk { .. }))
            .count()
    }

    /// Rejects malformed private keys: each `BindVk` must bind the output of an
    /// earlier `AssignUnboundVk`, and each `PrepareVerification` on a bound key
    /// must use the output of an earlier `BindVk`, all under the same guard,
    /// with as many public inputs as the key declares.
    pub(crate) fn validate_private_vks(&self) -> anyhow::Result<PrivateVks<'_>> {
        let mut vks = PrivateVks::default();
        let mut defined = HashSet::new();
        for ins in self.instructions.iter() {
            match ins {
                I::AssignUnboundVk {
                    guard,
                    nb_public_inputs,
                    output,
                    ..
                } => {
                    if !defined.insert(output) {
                        bail!("{} is bound to more than one key", output.0);
                    }
                    let info = PrivateVkInfo {
                        guard,
                        nb_public_inputs: *nb_public_inputs as usize,
                    };
                    vks.unbound.insert(output, info);
                }
                I::BindVk {
                    guard, vk, output, ..
                } => {
                    let info = match vk {
                        Operand::Variable(id) => vks.unbound.get(id),
                        Operand::Immediate(_) => None,
                    }
                    .ok_or_else(|| {
                        anyhow!("`bind_vk` takes an UnboundVk produced by `assign_unbound_vk`")
                    })?
                    .clone();
                    if info.guard != guard {
                        bail!(
                            "`bind_vk` on {:?} is guarded differently to the `assign_unbound_vk` that produced it",
                            vk
                        );
                    }
                    if !defined.insert(output) {
                        bail!("{} is bound to more than one key", output.0);
                    }
                    vks.bound.insert(output, info);
                }
                I::PrepareVerification {
                    guard,
                    vk: VkRef::Bound(vk),
                    instance,
                    ..
                } => {
                    let info = match vk {
                        Operand::Variable(id) => vks.bound.get(id),
                        Operand::Immediate(_) => None,
                    }
                    .ok_or_else(|| {
                        anyhow!(
                            "`prepare_verification` takes a BoundVk produced by `bind_vk`, got {vk:?}"
                        )
                    })?;
                    if info.guard != guard {
                        bail!(
                            "`prepare_verification` on {vk:?} is guarded differently to the `bind_vk` that produced it"
                        );
                    }
                    if instance.len() != info.nb_public_inputs {
                        bail!(
                            "`prepare_verification` passes {} public inputs, but the key {vk:?} declares {}",
                            instance.len(),
                            info.nb_public_inputs
                        );
                    }
                }
                _ => {}
            }
        }
        Ok(vks)
    }
}
