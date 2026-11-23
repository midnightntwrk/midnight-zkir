# ZKIR v4 — Recursive Verification (Delta Specification)

**Status:** Working draft.

**Versions covered:** ZKIR major version 4, minor version 0
(`IrMinorVersion::V0`). The JSON loader accepts only
`{ "major": 4, "minor": 0 }`.

This document specifies the parts of ZKIR 4 that verify inner proofs inside a
circuit: the accumulator types and instructions, fixed and private inner
verifying keys, the identity `vk_id` of an inner key, and the interface that
supplies private keys to the prover. It is a **delta** on the
[ZKIR v3 specification](zkir-v3-spec.md): all other types, instructions,
encodings and semantics are as specified there, with the changes that this
document gives.

The Rust implementation is the ultimate source of truth for behaviour. This
document is not mechanised: the Agda development in [../src/](../src/) covers
ZKIR v3 only, and no property in this document is machine-checked.

---

## Source pinning

| | |
|---|---|
| Repository | `midnightntwrk/midnight-zkir` (branch `alexshielded/unbound-vk`, based on `zkir-v4`) |
| Commit | `98eb8fbc` |
| Crate | `midnight-zkir`, `version = "4.0.0-rc.1"` |
| Dependencies | `midnight-zk-stdlib` 3.0.0-rc.1, `midnight-transient-crypto` 4.0.0 (ledger rev `9ec7289e`) |

### Files this document is derived from

| Rust file | Governs section(s) |
|---|---|
| `zkir/src/ir.rs` | §3 (syntax), §7 (key interface) |
| `zkir/src/ir_types.rs` | §2 (types) |
| `zkir/src/ir_instructions/unbound_vk.rs` | §4 (`vk_id`), §5.5, §5.6, §6 |
| `zkir/src/ir_instructions/prepare_verification.rs` | §5.1, §5.2, §6 |
| `zkir/src/ir_instructions/accumulate.rs` | §5.3, §5.4, §6 |
| `zkir/src/ir_vm.rs` | §5 (preprocess and circuit passes), §8 |
| `zkir/src/type_inference.rs` | §8.3 (chip selection) |
| `transient-crypto/src/proofs.rs` (midnight-ledger) | §8 (proof format, verification) |

---

## Table of contents

1. [Overview](#1-overview)
2. [Types](#2-types)
3. [Syntax](#3-syntax)
4. [Key identity: `vk_id`](#4-key-identity-vk_id)
5. [Instructions](#5-instructions)
6. [Static validation](#6-static-validation)
7. [Supplying private keys](#7-supplying-private-keys)
8. [Public inputs, proofs and verification](#8-public-inputs-proofs-and-verification)
9. [Producer obligations](#9-producer-obligations)
10. [Security considerations](#10-security-considerations)
11. [Limitations](#11-limitations)
12. [Appendix A — Worked example](#appendix-a--worked-example)

---

## 1. Overview

### 1.1 Conventions

The conventions of v3 §1.1 apply. In addition:

- An **inner proof** is a Midnight PLONK proof, with the Poseidon transcript,
  that a ZKIR circuit (the **outer** circuit) verifies.
- An **inner key** is the verifying key of an inner proof.
- `Poseidon(xs)` is the Poseidon hash of the `PoseidonChip` of
  `midnight-circuits` over `Fr`. Off-circuit and in-circuit, it is the same
  function.
- A **guard** is an operand that must resolve to `0` or `1`, as in v3.
- "Off" means that a guard resolves to `0`. "On" means that it resolves to `1`.

### 1.2 Model

The outer circuit does not complete the verification of an inner proof. It
does all the verification work except the final pairing check, and gives that
check to the outer verifier:

1. `inner_proof` binds the bytes of an inner proof to a name.
2. `prepare_verification` verifies the proof under an inner key, up to the
   pairing. It produces an **accumulator**: a pair of BLS12-381 G1 points whose
   pairing equation holds if and only if the proof is valid.
3. `accumulate` optionally folds two or more accumulators into one.
4. `verify_accumulator` makes an accumulator public. The outer proof carries
   it, and the outer verifier does its pairing check.

The inner key is one of these:

- A **fixed key**: circuit data. It is in `IrSource::inner_vks`, and
  `prepare_verification` names it by its `vk_id` (§4). The key is constant in
  the outer circuit.
- A **private key**: a prover witness. `assign_unbound_vk` witnesses it,
  `bind_vk` binds it to a `vk_id`, and `prepare_verification` uses the
  resulting `BoundVk`. One outer circuit can verify proofs under any private
  key of the required shape and size. The prover selects the key at proving
  time.

---

## 2. Types

ZKIR 4 adds three types to the v3 type set (v3 §2.2, §3). Their
`IrType` discriminants and string names are:

| Type | Discriminant | String name | `encoded_len` |
|---|---|---|---|
| `Accumulator` | 16 | `"Accumulator"` | `accumulator_pi_len()` |
| `UnboundVk` | 17 | `"UnboundVk"` | 0 |
| `BoundVk` | 18 | `"BoundVk"` | 0 |

### 2.1 `Accumulator`

- **Off-circuit value:** a `DeferredAccumulator`: two affine G1 points
  `(lhs, rhs)`. A value of this type is always **collapsed** and
  **fixed-base resolved**: each side is one point with scalar one.
- **In-circuit value:** an `AssignedAccumulator<Bls12>` with the same
  property. Instructions that encode or accumulate an accumulator check this
  property at synthesis, and fail if it does not hold.
- **Encoding:** the public-input form of the accumulator, of length
  `accumulator_pi_len()`. Decoding rejects a sequence that is not the
  encoding of a collapsed accumulator.
- **Trivial accumulator:** the accumulator that a guarded-off
  `prepare_verification` produces. Its pairing equation holds by
  construction.
- **Restrictions:** `copy` rejects an accumulator. Each accumulator must be
  consumed exactly once (§6.2).

### 2.2 `UnboundVk`

- **Off-circuit value:** a verifying key `VerifyingKey<Fr, KZG>`. Two values
  are equal if and only if their `transcript_repr` values are equal.
- **In-circuit value:** midnight-circuits' `UnboundVk<Fr, KZG>`: the key's
  `transcript_repr`, `k`, `omega` and commitments as witnesses. Nothing about
  the key is constrained, except that its commitments are points on the
  curve.
- **Origin:** only `assign_unbound_vk` produces this type.
- **Restrictions:** no encoding. It cannot be a circuit input, a transcript
  input or a constant: decoding, `assign` and `load_constant` of this type
  fail. In-circuit, encoding it fails, so it cannot be an output of a circuit
  with a communications commitment.

### 2.3 `BoundVk`

- **Off-circuit value:** a verifying key, as for `UnboundVk`.
- **In-circuit value:** midnight-circuits' `AssignedVk<Fr, KZG>`, returned by
  `bind_vk_to_hash`.
- **Origin:** only `bind_vk` produces this type.
- **Restrictions:** as for `UnboundVk`.

The in-circuit value of `UnboundVk` and `BoundVk` does not expose an
off-circuit value: its `value()` is unknown. The off-circuit value is in the
preprocess memory, and synthesis reads it from there.

---

## 3. Syntax

### 3.1 `IrSource`

ZKIR 4 adds one field to `IrSource`:

```
IrSource ::= ⟨ ...v3 fields...,
               inner_vks : [Bytes] ⟩
```

- Each entry of `inner_vks` is a fixed inner key, serialised by
  `MidnightVK::write` in the `Processed` format.
- In JSON, the field is optional. Its default value is the empty list. It is
  not written when it is empty.

### 3.2 `VkRef`

`prepare_verification` refers to its inner key with a `VkRef`:

```
VkRef ::= Fixed(Operand)   -- JSON: { "fixed": "0x<vk_id>" }
        | Bound(Operand)   -- JSON: { "bound": "%var" }
```

- `Fixed(op)`: `op` must be an immediate. Its value is the `vk_id` of an entry
  of `inner_vks`.
- `Bound(op)`: `op` must be a variable that a `bind_vk` instruction binds.

The binary tag of `VkRef` is `zkir-vk-ref[v1]`.

### 3.3 Instructions

ZKIR 4 appends six instructions to `Instruction`, in this order. The order
defines the binary layout (`ir-instruction[v4]`).

```
Instruction ::= ...v3 instructions...
  | PrepareVerification { guard : Operand, vk : VkRef,
                          instance : [Operand], proof : Identifier,
                          output : Identifier }
  | InnerProof          { guard : Operand, output : Identifier }
  | Accumulate          { inputs : [Operand], output : Identifier }
  | VerifyAccumulator   { input : Operand }
  | AssignUnboundVk     { guard : Operand, k : u8,
                          nb_public_inputs : u32, output : Identifier }
  | BindVk              { guard : Operand, vk : Operand, hash : Operand,
                          output : Identifier }
```

The JSON `op` names are `prepare_verification`, `inner_proof`, `accumulate`,
`verify_accumulator`, `assign_unbound_vk` and `bind_vk`.

---

## 4. Key identity: `vk_id`

Every inner key, fixed or private, has one identity, its `vk_id`. A key that
is published once can thus be verified as a fixed key or as a private key.

### 4.1 Definition

For a verifying key `vk` and a number of public inputs `n`:

```
vk_id(vk, n) = Poseidon([ TAG, Fr(n), vk_hash(vk) ])
```

- `TAG` is the byte string `"midnight-zkir:vk_id:v1"`, read as a
  little-endian integer in `Fr`. It separates `vk_id` from other Poseidon
  values.
- `vk_hash(vk)` is midnight-zk's hash of a verifying key:
  `Poseidon(transcript_repr ‖ k ‖ omega ‖ commitments)`, where
  `commitments` is the public-input form of the key's phase-0 commitments.
- `n` is the number of public inputs of the inner circuit. `vk_hash` does not
  cover it, so `vk_id` adds it.

The Rust function is `midnight_zkir::vk_id`.

### 4.2 Fixed keys

The `vk_id` of an entry of `inner_vks` is `vk_id(vk, n)`, where `vk` and `n`
are the verifying key and the number of public inputs that the
`MidnightVK` serialisation contains.

### 4.3 Stability

`vk_hash` covers `transcript_repr`. midnight-proofs computes
`transcript_repr` with a Blake2b hash that includes the `Debug` output of the
pinned constraint system. Thus:

- `vk_id` changes when midnight-proofs changes the definition of
  `transcript_repr`. Such a change also invalidates all existing keys and
  proofs.
- Only Rust code that uses the same midnight-proofs version can compute a
  `vk_id`.

A golden test (`vk_id_matches_the_golden_value` in
`zkir/tests/private_vk.rs`) records the `vk_id` of one fixed key. A change of
the definition makes this test fail.

---

## 5. Instructions

For each instruction, this section gives the preprocess rule (as v3 §6) and
the in-circuit rule (as v3 §7.2). `bool(op)` and `resolve(op)` are as in v3
§6.1.

### 5.1 `InnerProof { guard, output }`

**Preprocess.**

- Take the next entry of `P.inner_proofs`. One entry is consumed for each
  `inner_proof`, whatever its guard. Fail if no entry remains.
- If `bool(guard)` is `true`, bind `output` to the bytes of the entry.
  Otherwise, bind `output` to the empty byte string, and ignore the entry.
- After the run, fail if entries of `P.inner_proofs` remain.

The proof bytes are not a typed value: `output` can only be used as the
`proof` of a `prepare_verification`.

**In-circuit.** Bind `output` to the same bytes, as a free prover witness.
The instruction emits no constraints. The guard is not used in-circuit.

### 5.2 `PrepareVerification { guard, vk, instance, proof, output }`

**Preprocess.**

- Resolve each `instance[i]` to a `Native` value.
- If `bool(guard)` is `false`, bind `output` to the trivial accumulator. The
  key and the proof are not used.
- If `bool(guard)` is `true`:
  - Get the inner key: for `Fixed(id)`, the entry of `inner_vks` whose
    `vk_id` is `id`; for `Bound(b)`, the value of `b`. Fail if there is no
    such key.
  - Run the PLONK `prepare` step on `proof` with the Poseidon transcript, with
    no committed instance and with `instance` as the instance column. Fail if
    the proof cannot be read or the step fails.
  - Convert the result to an accumulator, resolve its fixed bases, and
    collapse it. Bind `output` to the result.

**Fixed bases.** The bases that are constant in the outer circuit are:

- For a fixed key: all the commitments of the key, and `-G`.
- For a bound key: only `-G`. The commitments of a private key are witnesses.

**In-circuit.**

- Convert the guard to an `AssignedBit`. This constrains it to be boolean.
- Get the in-circuit key: for a fixed key, the key assigned as constants
  (`assign_fixed_vk`); for a bound key, the `AssignedVk` value of the
  `BoundVk`.
- Run the in-circuit verifier's `prepare` on the proof witness, with a
  Poseidon transcript gadget, no committed instance, and `instance` as the
  instance column.
- Resolve the fixed bases, multiply the accumulator by the guard bit
  (`scale_by_bit`), and collapse it.

**Relation.** If the guard is `1`, the pairing equation of `output` holds if
and only if `proof` is a valid proof of `instance` under the key (subject to
the trust base, §10.6). If the guard is `0`, `output` is the trivial
accumulator, whatever the proof witness is.

### 5.3 `Accumulate { inputs, output }`

**Preprocess.** Fail if `|inputs| < 2`. Resolve each input to an
`Accumulator`. Fold them with `Accumulator::accumulate`, which uses Poseidon
to derive the folding challenges, and collapse the result. Bind `output` to
the result.

**In-circuit.** Check that each input is collapsed. Fold them with
`AssignedAccumulator::accumulate` and the Poseidon chip, and collapse the
result.

**Relation.** The pairing equation of `output` holds if the pairing equations
of all inputs hold. The converse holds except with negligible probability.

### 5.4 `VerifyAccumulator { input }`

**Preprocess.** Resolve `input` to an `Accumulator`. Append its public-input
form to the accumulator block of the public inputs (§8.1).

**In-circuit.** Check that the accumulator is collapsed. Constrain its
public-input form as public inputs.

The pairing check itself is done by the outer verifier (§8.2).

### 5.5 `AssignUnboundVk { guard, k, nb_public_inputs, output }`

**Preprocess.** Let `s` be the slot of this instruction: the number of
`assign_unbound_vk` instructions before it (§7.1).

- If `bool(guard)` is `true`:
  - Fail if no key is supplied for slot `s`.
  - Fail if the size of the supplied key is not `2^k`.
  - Fail if the constraint system of the key is not the finalised
    constraint system of an `INNER_ARCH` circuit of size `2^k` (§5.5.1). The
    comparison uses the `Debug` output of the pinned constraint systems.
  - Bind `output` to the key, as an `UnboundVk`.
- If `bool(guard)` is `false`: ignore slot `s`, and bind `output` to the
  **dummy key** of size `2^k` (§5.5.2).

These failures are errors, not panics.

**In-circuit.** Witness the key with `assign_unbound_vk`, against the
finalised `INNER_ARCH` constraint system of size `2^k`:

- The key's `transcript_repr`, `k` and `omega` are free witnesses.
- Its commitments are witnessed as curve points.
- The domain is derived from the witnessed `k` and `omega`: this requires
  `omega` to be invertible.

The guard is not used in-circuit. `bind_vk` enforces it (§5.6).

**Note.** In-circuit, the size `k` of the key is a witness. Only the hash in
`bind_vk` ties it to the instruction's `k`.

#### 5.5.1 `INNER_ARCH`

Every private key has one fixed shape: the `ZkStdLibArch` with every chip
enabled (Jubjub, Poseidon, SHA-256, SHA-512, SHA3-256, Keccak-256, BLAKE2b,
Secp256k1, P-256, BLS12-381, Curve25519, Base64, automaton),
`nb_arith_cols = 5` and `nr_pow2range_cols = 4`. The constraint system of a
size-`2^k` circuit is configured with `max_bit_len = k - 1`, as
`MidnightVK::read` does. Thus `k` must be at least 1.

The outer circuit is compiled against this constraint system before any key
is known. Thus the shape cannot vary at proving time.

#### 5.5.2 Dummy key

The dummy key of size `2^k` has the `INNER_ARCH` constraint system of size
`2^k`, and the BLS12-381 G1 generator as every commitment. It satisfies all
the checks of `assign_unbound_vk`, but no proof verifies under it. zkir
builds it once for each `k` and caches it.

### 5.6 `BindVk { guard, vk, hash, output }`

Let `n` be the `nb_public_inputs` of the `assign_unbound_vk` that produces
`vk` (§6.3).

**Preprocess.**

- Resolve `vk` to an `UnboundVk` and `hash` to a `Native`.
- If `bool(guard)` is `true`: fail if `vk_id(vk, n) ≠ hash`.
- Bind `output` to the key, as a `BoundVk`.

**In-circuit.**

- Convert the guard to an `AssignedBit`. This constrains it to be boolean.
- Witness `raw`, the off-circuit `vk_hash` of the key. Call
  `bind_vk_to_hash` with `raw`: this computes `vk_hash` of the witnessed key
  in-circuit and constrains it to equal `raw`. The result is the
  `AssignedVk`.
- Compute `id = Poseidon([TAG, Fr(n), raw])`, with `TAG` and `n` as
  constants.
- Constrain `id = select(guard, hash, id)`.
- Bind `output` to the `AssignedVk`, as a `BoundVk`.

**Relation.** If the guard is `1`, the witnessed key has `vk_id(key, n) =
hash`. If the guard is `0`, nothing about the key is constrained.

---

## 6. Static validation

Preprocess and synthesis both run these checks before they execute any
instruction. A violation is an error.

### 6.1 Inner proofs (`validate_inner_proofs`)

- Each `inner_proof` binds a fresh name.
- Each `prepare_verification` names, as `proof`, a name that an earlier
  `inner_proof` binds.
- The `prepare_verification` has the same `guard` operand as that
  `inner_proof`.
- Each bound proof is used by exactly one `prepare_verification`.

### 6.2 Accumulator lifecycle (`check_accumulator_lifecycle`)

An accumulator is produced by `prepare_verification`, `accumulate`, a circuit
input of type `Accumulator`, or `private_input`, `public_input` or
`load_constant` of type `Accumulator`. Each accumulator must be consumed
exactly once, by `accumulate` or `verify_accumulator`. Thus no accumulator is
dropped, and none is counted twice.

An accumulator that is not produced by `prepare_verification` or
`accumulate` is not checked in-circuit. Its pairing is still checked by the
outer verifier, as for every accumulator that reaches `verify_accumulator`.

### 6.3 Private keys (`validate_private_vks`)

- Each `assign_unbound_vk` and `bind_vk` binds a fresh name.
- The `vk` of each `bind_vk` is a variable that an earlier
  `assign_unbound_vk` binds.
- The `bind_vk` has the same `guard` operand as that `assign_unbound_vk`.
- The `vk` of each `prepare_verification` with a `Bound` key is a variable
  that an earlier `bind_vk` binds. A copy of a `BoundVk`, or an `UnboundVk`,
  is rejected.
- The `prepare_verification` has the same `guard` operand as that `bind_vk`.
- `|instance|` of the `prepare_verification` equals the `nb_public_inputs` of
  the `assign_unbound_vk` that produces the key.

One `BoundVk` can be used by more than one `prepare_verification`. Each use
needs its own `inner_proof`.

### 6.4 Fixed keys (`resolve_inner_vks`)

- Each entry of `inner_vks` must be a valid `MidnightVK` serialisation, so
  that its `vk_id` can be computed.
- No two entries have the same `vk_id`.
- The `vk` of each `prepare_verification` with a `Fixed` key is an immediate,
  and an entry of `inner_vks` has that `vk_id`.
- Each entry is used by at least one `prepare_verification`.

---

## 7. Supplying private keys

Private keys do not travel in the `IrSource` or the `ProofPreimage`. The
prover supplies them out of band.

### 7.1 Slots

A circuit has one **slot** for each `assign_unbound_vk` instruction, in
instruction order. `IrSource::inner_vk_slots()` returns the number of slots.
The slot index of an instruction is fixed by the circuit. It does not depend
on the path that the guards select.

### 7.2 Interface

```rust
pub type InnerVerifyingKey = VerifyingKey<Fr, KZG>;

impl IrSource {
    pub fn inner_vk_slots(&self) -> usize;
    pub fn check_with_inner_vks(
        &self, preimage: &ProofPreimage,
        inner_vks: &[Option<InnerVerifyingKey>],
    ) -> Result<Vec<Option<usize>>, ProvingError>;
    pub async fn prove_with_inner_vks(
        &self, rng, params, pk, preimage: &ProofPreimage,
        inner_vks: &[Option<InnerVerifyingKey>],
    ) -> Result<(Proof, Vec<Fr>, Vec<Option<usize>>), ProvingError>;
}
```

- `inner_vks` must have exactly `inner_vk_slots()` entries. Otherwise both
  functions fail.
- Entry `s` is the key for slot `s`. `None` means that no key is supplied.
  This is permitted only for a slot whose instruction is guarded off.
- `Zkir::check` and `Zkir::prove` are equal to these functions with an empty
  `inner_vks`. They thus fail for a circuit that has a slot.
- Key generation does not use private keys: the outer circuit depends only on
  the shape and the size of the keys.

### 7.3 Integration *(informative)*

The intended integration is a method of the midnight-ledger `Resolver` that
fetches the key for a slot, and `Zkir` trait methods with default
implementations that call `check_with_inner_vks` and `prove_with_inner_vks`.
These changes are not part of this pin.

---

## 8. Public inputs, proofs and verification

### 8.1 Public-input layout

ZKIR 4 adds an accumulator block in front of the v3 public inputs (v3 §7.3):

```
π = acc_block ++ [binding_input] (++ [comm_commitment])? ++ (Impact groups…)
acc_block = encode(acc₁) ++ … ++ encode(acc_m)
```

- `acc₁ … acc_m` are the inputs of the `verify_accumulator` instructions, in
  instruction order. `m` is `accumulator_count()`, the number of
  `verify_accumulator` instructions. `m` is a property of the source: it does
  not depend on the guards.
- Each block has length `accumulator_pi_len()`.

### 8.2 Proof format and verification

- `Zkir::prove` returns a `Proof` that contains the PLONK proof bytes and the
  accumulators `acc₁ … acc_m`. The returned statement is the part of `π`
  after `acc_block`.
- The `VerifierKey` records `m`. Verification:
  1. Fail if the proof does not carry exactly `m` accumulators.
  2. Verify the PLONK proof against `acc_block ++ statement`.
  3. Fail if the pairing check of any accumulator fails.

### 8.3 Chip selection

The types pass enables the BLS12-381 and Poseidon chips for a circuit that
binds a value of type `Accumulator`, `UnboundVk` or `BoundVk`.

---

## 9. Producer obligations

These are additions to v3 §8.2. They are the responsibility of the producer
of the IR, in practice the Compact compiler.

- **O5 — Trusted hash.** The `hash` of each `bind_vk` must be a value that
  the verifier controls: a constant, a value made public with `impact`, a
  member of a public set, or a value bound by other means. If the prover can
  choose `hash` freely, the circuit proves only "I know a proof under *some*
  key", which any prover can satisfy.
- **O6 — Shared guards.** One guard operand is used by each
  `inner_proof`/`prepare_verification` pair, and by each
  `assign_unbound_vk`/`bind_vk`/`prepare_verification` chain. §6 enforces
  this.
- **O7 — Every accumulator is verified.** Each accumulator reaches exactly
  one `verify_accumulator`, possibly through `accumulate`. §6.2 enforces
  this.
- **O8 — Inner shape.** An inner circuit whose key is supplied privately must
  have the `INNER_ARCH` shape (§5.5.1). Its proofs must use the Poseidon
  transcript and have no committed instance.

---

## 10. Security considerations

### 10.1 Soundness of private keys

The private key is a prover witness. Only `bind_vk` constrains it. The checks
of §5.5 that run off-circuit (size, shape, hash) protect an honest prover
from mistakes. They give no guarantee to the verifier. A test
(`bind_vk_is_enforced_in_circuit`) checks that a prover that skips the
off-circuit checks cannot make a valid proof with a key that does not match
the hash.

### 10.2 The identity of the key is not hidden

If `hash` is public, as O5 usually requires, any party can compare it with
published `vk_id`s. The proof then discloses which key it was verified under.
To hide the key, the producer must prove that `hash` is a member of a public
set of keys (for example, with a Merkle tree over `vk_id`s), and not make
`hash` public.

### 10.3 The size of the inner circuit is not hidden

`k` is a constant of `assign_unbound_vk`, and thus of the outer circuit. The
outer circuit discloses the size of the inner circuit. With set membership,
a key is only indistinguishable from the other keys of the same size.

### 10.4 The shape of the inner circuit

All private keys have the `INNER_ARCH` shape. The shape thus discloses
nothing. The cost is that each inner circuit configures every chip, and that
the outer circuit witnesses, and hashes, every commitment of the key.

A change of the stdlib configuration that `INNER_ARCH` depends on changes the
constraint system that the outer circuit is compiled against, and the `vk_id`
of every inner key. Such a change needs a new instruction or IR version.

### 10.5 Untrusted key bytes

Fixed keys in `inner_vks` are parsed by `MidnightVK::read` in the `Processed`
format, which checks that each point is on the curve and in the subgroup.
Private keys are supplied as parsed `VerifyingKey` values. The supplier is
responsible for their parsing.

### 10.6 Trust base

In addition to the v3 trust base (v3 §8.6), this document trusts:

- The in-circuit verifier of midnight-circuits (`prepare`,
  `assign_unbound_vk`, `bind_vk_to_hash`, accumulator folding and collapse),
  and its agreement with the off-circuit verifier of midnight-proofs.
- Poseidon, as a collision-resistant hash and as the source of the folding
  challenges of `accumulate`.
- The KZG commitment scheme over BLS12-381, and the pairing check that the
  outer verifier does.

---

## 11. Limitations

- **Not mechanised.** No property of this document is machine-checked. The
  Agda development covers ZKIR v3 only.
- **v3 additions not covered.** The v3 specification is pinned before
  `Bytes(n)`, `Byte`, `Bool`, `Sha512` and related instructions. This
  document does not cover them either.
- **One shape.** Private keys have only the `INNER_ARCH` shape (§10.4).
- **Dummy key format.** The dummy key (§5.5.2) is built from the
  midnight-proofs key serialisation, version `0x03`. A change of that format
  makes guarded-off proving fail with an error.
- **Ledger integration.** The `Resolver` and `Zkir` trait changes of §7.3 are
  not implemented.

---

## Appendix A — Worked example

The circuit below verifies one inner proof under a private key, if the guard
`%g` is `1`. The inner circuit has one public input, `%s`. The circuit makes
the key's `vk_id` `%h` public with `impact`, so the verifier knows which key
the proof was verified under (O5). The value of `k` is an example: it must be
the size of the inner circuit.

```json
{
  "version": { "major": 4, "minor": 0 },
  "inputs": [
    { "name": "%h", "type": "Scalar<BLS12-381>" },
    { "name": "%g", "type": "Scalar<BLS12-381>" },
    { "name": "%s", "type": "Scalar<BLS12-381>" }
  ],
  "outputs": [],
  "do_communications_commitment": false,
  "instructions": [
    { "op": "impact", "guard": "%g", "inputs": ["%h"] },
    { "op": "inner_proof", "guard": "%g", "output": "%p" },
    { "op": "assign_unbound_vk", "guard": "%g", "k": 15,
      "nb_public_inputs": 1, "output": "%u" },
    { "op": "bind_vk", "guard": "%g", "vk": "%u", "hash": "%h",
      "output": "%b" },
    { "op": "prepare_verification", "guard": "%g", "vk": { "bound": "%b" },
      "instance": ["%s"], "proof": "%p", "output": "%a" },
    { "op": "verify_accumulator", "input": "%a" }
  ]
}
```

**Proving, guard on.** The preimage has `inputs = [vk_id, 1, s]`,
`public_transcript_inputs = [vk_id]` and `inner_proofs = [proof]`. The prover
calls `prove_with_inner_vks` with `[Some(key)]`.

**Proving, guard off.** The preimage has `inputs = [h, 0, s]` for any `h` and
`s`, no public transcript inputs, and `inner_proofs = [blank]`. The prover
calls `prove_with_inner_vks` with `[None]`. zkir uses the dummy key. The
accumulator is trivial.

**Public inputs.** `π = encode(acc) ++ [binding_input, select(g, h, 0)]`.
The proof carries `acc`. The returned statement is
`[binding_input, select(g, h, 0)]`.

For the same circuit with a fixed key, remove the `assign_unbound_vk` and
`bind_vk` instructions, add the serialised key to `inner_vks`, and use
`"vk": { "fixed": "0x<vk_id>" }`.
