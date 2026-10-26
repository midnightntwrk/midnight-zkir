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
//! bound to a trusted hash (`BindVk`).

use std::sync::Arc;

use anyhow::bail;
use midnight_circuits::{
    hash::poseidon::PoseidonChip,
    types::AssignedNative,
    verifier::{UnboundVk, vk_hash},
};
use midnight_proofs::{
    circuit::{Layouter, Value},
    plonk::{ConstraintSystem, Error, VerifyingKey},
    utils::SerdeFormat,
};
use midnight_zk_stdlib::{KZG, ZkStdLib, ZkStdLibArch};
use transient_crypto::curve::Fr;

use crate::{
    ir_instructions::{F, encode::decode_offcircuit},
    ir_types::{BYTES_PER_FIELD_ELEMENT, CircuitValue, InnerVk, IrType, IrValue},
};

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

/// The constraint system of an inner circuit of size `2^k`, as configured when
/// reading its `MidnightVK`.
fn inner_cs(k: u8) -> Result<ConstraintSystem<F>, Error> {
    let max_bit_len = k
        .checked_sub(1)
        .ok_or_else(|| Error::Synthesis("AssignUnboundVk: k must be positive".into()))?;
    let mut cs = ConstraintSystem::default();
    ZkStdLib::configure(&mut cs, (INNER_ARCH, max_bit_len));
    Ok(cs)
}

/// Reads the verifying key of an inner circuit of size `2^k` from the front of
/// `transcript`, where it is serialized (`VerifyingKey::write`, `Processed`
/// format) and packed as a `Bytes` value.
///
/// Returns the key and the number of field elements it takes.
pub fn assign_unbound_vk_offcircuit(
    transcript: &[Fr],
    k: u8,
) -> Result<(IrValue, usize), anyhow::Error> {
    // The length of the key is only known once it is read, so the encoding of
    // its bytes is checked afterwards.
    let bytes: Vec<u8> = (transcript.iter())
        .flat_map(|x| x.0.to_bytes_le().into_iter().take(BYTES_PER_FIELD_ELEMENT))
        .collect();
    let mut reader = bytes.as_slice();
    let vk = VerifyingKey::read_from_cs(&mut reader, SerdeFormat::Processed, inner_cs(k)?)?;
    let len = bytes.len() - reader.len();
    let nb_elements = len.div_ceil(BYTES_PER_FIELD_ELEMENT);
    decode_offcircuit(&transcript[..nb_elements], &IrType::Bytes(len as u32))?;

    if vk.get_domain().k() != k as u32 {
        bail!(
            "AssignUnboundVk: expected a key of size 2^{k}, got 2^{}",
            vk.get_domain().k()
        );
    }
    Ok((IrValue::UnboundVk(InnerVk(Arc::new(vk))), nb_elements))
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
    let cs = inner_cs(k)?.into_finalized();
    std_lib
        .verifier::<KZG>()
        .assign_unbound_vk(layouter, vk.as_ref().map(|vk| vk.0.as_ref()), &cs)
        .map(CircuitValue::UnboundVk)
}

/// Checks that `vk` hashes to `hash`.
pub fn bind_vk_offcircuit(vk: IrValue, hash: IrValue) -> Result<(), anyhow::Error> {
    let vk: InnerVk = vk.try_into()?;
    let hash: Fr = hash.try_into()?;
    if vk_hash::<PoseidonChip<F>, F, KZG>(&vk.0) != hash.0 {
        bail!("BindVk: the verifying key does not match the given hash");
    }
    Ok(())
}

/// Constrains `vk` to hash to `hash`.
pub fn bind_vk_incircuit(
    std_lib: &ZkStdLib,
    layouter: &mut impl Layouter<F>,
    vk: CircuitValue,
    hash: CircuitValue,
) -> Result<(), Error> {
    let vk: UnboundVk<F, KZG> = vk.try_into()?;
    let hash: AssignedNative<F> = hash.try_into()?;
    std_lib
        .verifier::<KZG>()
        .bind_vk_to_hash(layouter, std_lib.poseidon_chip(), vk, &hash)
        .map(drop)
}
