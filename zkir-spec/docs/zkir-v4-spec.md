# ZKIR v4 language specification

This reference specifies ZKIR 4.0 at the `zkir-4.0.0-rc.1` release tag, commit `3ec876c0a311e4979536ae432d2c810e324ace64`.  It covers the source format, witness preprocessing, the circuit relation at the chip interface, and proving and verification with fixed inner verifying keys.  The [v3 specification](zkir-v3-spec.md) has its own source and proof scope.  [Pinned Rust source](https://github.com/midnightntwrk/midnight-zkir/tree/3ec876c0a311e4979536ae432d2c810e324ace64)

| Dependency versions | Revision in the release lockfile |
| --- | --- |
| `midnight-ledger` (`transient-crypto` 4.0.0-rc.0, `base-crypto` 1.1.1, `serialize` 1.2.1) | `eb784a9bba926cb71eaf199a99b3949cc2885a87` |
| `midnight-zk` (`midnight-zk-stdlib` 3.0.0-rc.2, `midnight-circuits` 8.0.0-rc.2, `midnight-curves` 0.4.0-rc.2, `midnight-proofs` 0.9.0-rc.2) | `4575056ad96a2e70321f0bd8577dea2cd8d8b2e3` |
| `blake2b_halo2` 0.3.0-rc.1 | `6d9828c922f5cecf0d4f0666a119581abe7ff950` |
| `sha3-circuit` 0.3.0-rc.1 | `a66a403a55bc9531d9084eef2923c6353d763edf` |

[Release tag](https://github.com/midnightntwrk/midnight-zkir/tree/zkir-4.0.0-rc.1) · [Release Cargo.lock](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/Cargo.lock)

## Overview

ZKIR is the circuit language emitted by Midnight's Compact compiler.  A source describes a straight-line computation on named, typed values and the constraints that make its result verifiable.  The author of a contract chooses which facts to expose.  Reading a transcript, returning a value, and publishing a field each have a different effect on what the verifier can check.  [Worked contract example](#74-a-hash-preimage-and-its-public-nullifier)

| Stage | Input | Result |
| --- | --- | --- |
| Compile | A ZKIR source (`.zkir` JSON or `.bzkir` tagged binary) and public proving parameters | The `zkir compile` command generates the proving and verifying keys.  `compile-many` handles a directory.  `mock-compile` reports the circuit cost, including rows and size parameter `k`. |
| Prove | The source, its proving key, parameters and a call's proof preimage | The prover preprocesses the call, uses the resulting witness to prove the circuit, and returns a proof, an external statement and impact skip information. |
| Verify | The source's verifying key, verifier parameters, the proof and the caller-supplied statement | The ledger prepends the encodings of the accumulators carried by the proof to the statement, verifies the outer proof on that full instance, and checks each deferred pairing. |

The proving key can be reused for different calls to the same circuit.  The caller chooses the verifying key and the statement it expects.  [Compiler commands](../../zkir/src/main.rs) · [Proving and verification](#6-proving-and-verification)

## 1. Source and representation

An `IrSource` contains a version, ordered typed input names, an ordered output type signature, a Boolean communications commitment flag, a sequence of instructions, and a table of fixed inner verifying keys.  Instructions operate on typed values by name in one straight-line sequence.  Each ordinary operand is either a lookup in the value store or a native field immediate.  Proof identifiers use a separate store of opaque byte blobs.  Instruction results bind identifiers as evaluation proceeds.  A producer gives each declared input and each value result a fresh name in the value store, so later references denote the same value in both passes.

In the abstract syntax below, brackets denote ordered lists.  The two kinds of name have the same identifier representation.  The instruction determines which store supplies a lookup or receives a binding.

```text
Source       ::= (V0, [TypedInput], [Type], CommitFlag, [Instruction], [KeyBytes])
TypedInput   ::= (ValueName, Type)
Operand      ::= Variable(ValueName) | Immediate(NativeFieldElement)
ValueName    ::= Identifier
ProofName    ::= Identifier
KeyBytes     ::= [Byte]
CommitFlag   ::= true | false
```

Section 2 defines `Type`.  The signatures in §4 complete the grammar for `Instruction`.  For example, `InnerProof` binds a `ProofName`, and the `proof` field of `PrepareVerification` reads that name.  The latter instruction binds its accumulator result to a `ValueName`.  [Abstract syntax](../src/zkir-v4/Syntax.agda)

The Rust VM checks proof bindings, accumulator use and fixed-key table coverage before preprocessing or synthesis.  Preprocessing then checks the operands and streams as it executes.  The stronger Agda predicate `Producer`, decided by `producer?`, also checks single assignment, operand scope and types, instruction-specific widths and arities, and placement of the final `Output`.  The correspondence theorems in §8 use this producer discipline.  [Rust preprocessing](../../zkir/src/ir_vm.rs#L238) · [Agda producer checker](../src/zkir-v4/Producer.agda)

`IrSource::load` accepts a JSON object with `"version": {"major": 4, "minor": 0}`.  The remaining top-level fields are `inputs`, `outputs`, `do_communications_commitment`, `instructions`, and optional `inner_vks` (default `[]`).  A typed input has fields `name` and `type`.  Each instruction has an `op` tag with its snake-case spelling and the fields listed in [§4](#4-instructions).  JSON ordinary operands are strings.  Variable references begin with `%`.  Immediates start with `0x` or `0X` and contain hex-encoded little-endian bytes representing an integer below the native field order, optionally preceded by a minus sign for field negation.  For example, `"0x0001"` denotes 256.  The hexadecimal payload must contain 1 to 32 whole bytes (2 to 64 digits).  A high zero byte counts toward this limit.  `load_constant.encoding` is an array of immediate strings and `prepare_verification.vk_hash` is a hex byte string.  `inner_vks` is an array of byte arrays.  [JSON loader and instruction definitions](../../zkir/src/ir.rs) · [Native field decoder](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/curve.rs#L344-L354)

The tagged binary format uses the pinned ledger `serialize` crate.  Source input uses `load_ir_from_tagged`.  The source payload serializes its fields in their Rust declaration order and encodes the minor version as variant zero.  The instruction table lists the zero-based variant discriminants.  Each variant's payload serializes its fields in declaration order.  Operand variant 0 carries an identifier.  For variant 1 the writer serializes the field value as lowercase little-endian hex with a `0x` prefix.  It drops high zero bytes, keeping one byte for zero.  Thus JSON operands `"0x2a00"` and `"0X2A"` both serialize with the string payload `"0x2a"`.  A binary type discriminant selects the type in [§2](#2-types-and-encodings).  It carries a serialized `u32` length only for discriminant 15.  The decoder rejects zero, 32 and values above 2²⁴ for discriminant 15.  [Tagged serialization](../../zkir/src/ir.rs) · [Type serialization](../../zkir/src/ir_types.rs)

| Object | Tag |
| --- | --- |
| Source | `ir-source[v4-generic]` |
| Instruction | `ir-instruction[v4]` |
| Type | `ir-type[v2]` |
| Identifier | `zkir-identifier[v1]` |
| Typed identifier | `zkir-typed-identifier[v2]` |
| Operand | `zkir-operand[v1]` |
| Minor version | `ir-minor-version[v4]` |
| Prover key for this source | `prover-key[v8](ir-source[v4-generic])` |

The tagged prover key read by `load_prover_key_from_tagged` wraps a length-prefixed raw key byte vector.  The separate raw format read by `read_raw_pk` is gzip-compressed `MidnightPK` in `RawBytesUnchecked` format.  The writer uses gzip level 6.  The relation embedded in the key is itself a length-prefixed tagged source.  [Key methods](../../zkir/src/ir.rs) · [Relation serialization](../../zkir/src/ir_vm.rs#L1861) · [Ledger prover key](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/proofs.rs#L270-L394)

The backend writes architecture format version 4 into the keys.  Keys generated with `midnight-zk-stdlib` 3.0.0-rc.1 are incompatible for every circuit.  Regenerate both keys with the release backend.  For a recursive source, regenerate child keys first, replace their processed bytes in `inner_vks` and their SHA-256 digests in the preparation instructions, then generate the parent keys.  [Release key compatibility](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/CHANGELOG.md#L35-L41) · [Architecture reader](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/zk_stdlib/src/lib.rs#L211-L246)

## 2. Types and encodings

Let `F` be the BLS12-381 scalar field, also the Jubjub base field.  Write ⟦x⟧ for the canonical unsigned integer representative of a field element.  The native bit width is 255 and 31 whole bytes always fit in one native element.  The `Bool` and `Byte` types are separate from `Native`.  In particular, a guard or selector uses a `Native` with value zero or one.  `Bytes(n)` is a byte string of exactly `n` bytes for `1 ≤ n ≤ 2²⁴`.  Its JSON length uses decimal digits with no leading zero.  Edwards point types are in the prime-order subgroups.  An `Accumulator` is a pair of BLS12-381 G1 points with implicit unit scalars, one point per side of the deferred KZG pairing.  [Rust type and value definitions](../../zkir/src/ir_types.rs)

| Type | JSON | Binary | Width in `F` | Typed encoding |
| --- | --- | ---: | ---: | --- |
| `Native` | `Scalar<BLS12-381>` | 0 | 1 | One field element |
| `Bool` | `Bool` | 13 | 1 | Zero or one |
| `Byte` | `Byte` | 14 | 1 | Integer in `[0, 256)` |
| `Bytes(n)` | `Bytes<n>` | 1 for 32, 15 otherwise | ⌈n/31⌉ | Little-endian chunks |
| `JubjubPoint` | `Point<Jubjub>` | 2 | 2 | Affine `x, y` |
| `JubjubScalar` | `Scalar<Jubjub>` | 3 | 1 | Canonical scalar integer |
| `Secp256k1Point` | `Point<Secp256k1>` | 4 | 5 | Encoded `x`, encoded `y`, identity flag |
| `Secp256k1Base` | `Base<Secp256k1>` | 5 | 2 | Foreign-field limbs |
| `Secp256k1Scalar` | `Scalar<Secp256k1>` | 6 | 2 | Foreign-field limbs |
| `Secp256r1Point` | `Point<Secp256r1>` | 7 | 5 | Encoded `x`, encoded `y`, identity flag |
| `Secp256r1Base` | `Base<Secp256r1>` | 8 | 2 | Foreign-field limbs |
| `Secp256r1Scalar` | `Scalar<Secp256r1>` | 9 | 2 | Foreign-field limbs |
| `Curve25519Point` | `Point<Curve25519>` | 10 | 4 | Encoded `x`, encoded `y` |
| `Curve25519Base` | `Base<Curve25519>` | 11 | 2 | Foreign-field limbs |
| `Curve25519Scalar` | `Scalar<Curve25519>` | 12 | 2 | Foreign-field limbs |
| `Accumulator` | `Accumulator` | 16 | 12 | Encoded left point, 1, encoded right point, 1 |

### 2.1 Typed encoding

`encode(v)` maps a typed value to native field elements.  `decode(t, w)` succeeds when `w` has the width prescribed for `t`, the type decoder succeeds, and re-encoding the result reproduces `w` exactly.  [Rust codec dispatch](../../zkir/src/ir_instructions/encode.rs)

For a foreign field of order `p`, let `u = (x − 1) mod p` be the least nonnegative representative.  The public-input codec writes `[u mod 2ᵏ, ⌊u / 2ᵏ⌋]`, low part first.  For the Secp256k1 and Secp256r1 base and scalar fields and the Curve25519 base field, `k = 192` (three 64-bit limbs in the first native element).  For the Curve25519 scalar field, `k = 204` (four 51-bit limbs).  For example, `Base<Secp256k1>` value `2¹⁹² + 5` has typed encoding `[4, 1]`.  A `load_constant` for that value takes `"encoding": ["0x04", "0x01"]`.  The pinned definitions are normative for the field encodings.  [AssignedField public-input codec](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/field/foreign/field_chip.rs#L121-L164) · [Field parameters](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/field/foreign/params.rs#L182-L382)

A foreign point encodes its affine `x` fields followed by its `y` fields.  A Weierstrass point appends a native identity flag, zero for an ordinary point and one for the identity.  For the identity it applies the coordinate field codec to `(0, 0)`.  The Edwards identity has affine coordinates `(0, 1)`.  Each accumulator side encodes a BLS12-381 G1 point followed by its unit scalar.  The G1 coordinates use the same shifted-field rule with `k = 224` (four 56-bit limbs in the first element), giving five fields per point including its identity flag.  The decoder checks the canonical encoding of each point and unit scalar.  A decoded accumulator may still fail the pairing check.  [Weierstrass codec](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/ecc/foreign/weierstrass_chip.rs#L238-L256) · [Foreign Edwards codec](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/ecc/foreign/edwards_chip.rs#L326-L339) · [Accumulator codec](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/proofs.rs#L398-L552)

For bytes, partition `v` from the first byte into contiguous chunks of at most 31.  Pack chunk `b₀…bᵣ₋₁` as `Σ bᵢ·256ⁱ`.  For each chunk of width `r`, decoding requires the corresponding field element to be below `256ʳ`, then emits exactly `r` little-endian bytes.  The last field of a 32-byte encoding must be below 256.  Leading and trailing zero bytes remain part of the declared length.  This encoding governs declared inputs, typed transcript reads, constants, `Encode`, and the encoded input and return values in the communications commitment.  [Byte codec](../../zkir/src/ir_instructions/encode.rs)

### 2.2 Byte conversion

`ToBytes` on a prime-field type emits the canonical integer in 32 little-endian bytes.  `FromBytes` to a prime-field type interprets its byte string as a little-endian unsigned integer and reduces it modulo the destination field order.  Any supported byte-string length is allowed for the reduction.  A 32-byte encoding of the native field order therefore reduces to native zero through `FromBytes`.  If parsed as a typed `Native` field immediate, that integer is out of range.

For Jubjub and Curve25519 points the compressed representation has the 32 little-endian bytes of the `y` coordinate with the parity of `x` in the high bit.  The Edwards identity encodes as byte 1 followed by 31 zero bytes.  For Secp256k1 and Secp256r1 the representation has a SEC1 prefix `0x02` or `0x03` followed by the 32 big-endian bytes of the `x` coordinate.  For each of the latter two curves, the 33-byte string of zeros represents the identity.  Decoding points checks the length, decodes into the point type, and requires equality to the canonical re-encoding.  It rejects wrong lengths, off-curve points, points outside the relevant subgroup, and noncanonical bytes, including an alternate sign for an Edwards point with `x = 0`.  Synthesis for point decoding assigns the decoded point and constrains its compressed encoding to equal the operand bytes.  [Byte encoding](../../zkir/src/ir_instructions/to_bytes.rs) · [Byte decoding](../../zkir/src/ir_instructions/from_bytes.rs)

## 3. Two execution passes

For a source `S` that synthesizes, write `C(S)` for the constraints and the ordered public cells determined by its instructions.  Write `C(S; π, w)` when the assignment `w` satisfies every constraint and the public cells equal the field vector `π`.  The **circuit relation** on instances is therefore `Rₛ(π) ≡ ∃ w. C(S; π, w)`.  The external statement supplied to the ledger is a suffix of `π`.  For a source with no accumulator exposures it is the whole vector.  [Circuit model](../src/zkir-v4/Circuit.agda) · [Instance layout](#6-proving-and-verification)

Preprocessing executes on `IrValue`s, such as a native field element, a point, or a byte string.  During synthesis a `CircuitValue` represents the corresponding assigned cell or collection of cells.  The source fixes how those cells are wired even when their values are unknown at key generation.  The **honest witness** draws its named values, full public input and ordered proof-slot bytes from a successful VM run, together with the binding input and optional commitment pair from the preimage.  Whether this witness satisfies `C(S)`, and whether an arbitrary satisfying witness explains a legal run, are the two different questions in §8.  [Rust value representations](../../zkir/src/ir_types.rs) · [Honest witness](../src/zkir-v4/CircuitProof.agda)

### 3.1 Preprocessing

The preimage carries the ordered raw declared inputs, a native `binding_input`, an optional pair `(commitment, randomness)`, and a key location for the proving interface.  Each of its four streams has an independent cursor.

| Preimage stream | Consumer | Active guard | Zero guard |
| --- | --- | --- | --- |
| `public_transcript_inputs` | `Impact` | Match and consume one native field per operand. | Consume nothing.  Append one zero per operand to the statement. |
| `public_transcript_outputs` | `PublicInput` | Decode and consume the declared type's width in fields. | Consume nothing.  Bind the typed default. |
| `private_transcript` | `PrivateInput` | Decode and consume the declared type's width in fields. | Consume nothing.  Bind the typed default. |
| `inner_proofs` | `InnerProof` | Consume one `Direct` blob and bind its bytes. | Consume one `Direct` blob and bind the empty byte string. |

Before the walk, preprocessing checks the proof bindings, accumulator uses, and key table (§5).  It decodes the declared inputs in order and requires exact consumption of their raw vector.  It initializes all four cursors to zero, the accumulator public-input block to empty, and the external statement block to the binding input followed by the supplied commitment if enabled.  With commitment enabled, the pair `(c, r)` must be supplied.  With commitment disabled, the optional pair is ignored by the relation.  The return value list and the impact skip list both start empty.

The walk applies the rules in [§4](#4-instructions).  An omitted guard on a typed read means the read is active.  The defaults are zero for a field or byte, false for `Bool`, the all-zero string of the specified length for bytes, and the group identity for points.  For `Accumulator`, `trivial_accumulator()` gives the G1 identity with scalar one on each side, so the deferred pairing equation holds.  [Default values](../../zkir/src/ir_types.rs#L535) · [Trivial accumulator](../../zkir/src/ir_instructions/accumulate.rs#L34-L39)

For each active `PublicInput` or `PrivateInput`, the corresponding stream must contain at least the declared type’s width in fields at the current cursor.  An active `Impact` requires matching transcript fields, and every `InnerProof` requires a proof slot.

At the end all four streams must be exhausted exactly, including placeholder proof slots for inactive proofs.  For a nonempty return signature, `producer?` requires a single `Output` as the final instruction.  Its operands must match the declared return types in order and supply the return values.  An empty signature permits either no `Output` or a single final `Output` with no operands.  `check` runs preprocessing and returns only the skip list.  [Preprocessing](../../zkir/src/ir_vm.rs#L238) · [Proof preimage](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/proofs.rs#L1108-L1131)

With commitment enabled, let `message = raw_inputs ++ encode(returns)`, where the encodings of successive return values are concatenated in order.  The ledger function `transient_commit(message, r)` hashes the native-field sequence `[r] ++ message` with Poseidon.  Preprocessing requires this hash to equal the supplied `c`.  For example, one native input 7, one native return 8 and randomness 9 give the hash input `[9, 7, 8]`.  With binding input 99 and no impacts, the external statement is `[99, c]`.  [Ledger commitment](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/hash.rs#L84-L88) · [VM commitment check](../../zkir/src/ir_vm.rs#L972-L983)

### 3.2 Circuit synthesis

Synthesis walks the same sequence on assigned cells.  Native immediates and `LoadConstant` are fixed assignments.  Declared inputs and typed transcript reads assign cells of the specified type from witness memory.  Proof bindings supply byte witnesses by position for the recursive verifier gadget.  Derived cells use the operation-specific contracts in [§4](#4-instructions).  Synthesis can construct its layout without a known witness.  With a known preprocessing result, the implementation checks several assignments against the stored values.  These diagnostics add no gates.

Agda’s `satisfies-constraints` checks the assigned cells and public instance with these diagnostics disabled.  The replay relation `satisfies` also checks any supplied values for computed names.  For a producer source, `public-instance-equivalence` proves that both relations accept the same public instances.  To run the diagnostics, keep the witness values used for declared inputs and transcript reads, and omit the optional entries for computed names.  Single assignment ensures that this preserves the values read by the circuit, and the final circuit state is the same.  [Diagnostic equivalence](../src/zkir-v4/CircuitDiagnostics.agda)

`PublicInput` and `PrivateInput` have the same synthesis behavior: each assigns a free typed witness value and omits the guard from constraints.  Thus an inactive read's default is enforced by preprocessing alone.  `Impact` converts its guard to a bit and resolves every operand as `Native` even when the guard is false.  It exposes a selection between the operand and zero.  `VerifyAccumulator` exposes the accumulator encoding inline.  All the external statement cells are exposed after the walk, with the binding input first, then the commitment if enabled, then impact fields in instruction order.  With commitment enabled, the circuit constrains `c` to the Poseidon hash of the sequence in §3.1.  It reconstructs the input portion by encoding the declared names from final witness memory in declaration order.  Single assignment preserves their initial values, whose encodings reproduce `raw_inputs`.  [Synthesis](../../zkir/src/ir_vm.rs#L1031)

The types pass computes types for intermediate assignments to select required chips.  It copies the appropriate operand type for same-result-type operations, derives curve and coordinate types from their input types, uses explicit types for reads and conversions, and computes byte lengths for byte operations.  The pass enables the curve chips for encountered types, BLS12-381 and Poseidon for accumulators, the hash-specific chips for hash instructions, and Poseidon for the communications commitment.  ZKIR requests one range-check group, which uses five advice columns.  It leaves the lane width unset.  For a circuit of size 2ᵈ the backend therefore uses max(1, d − 1) bits per lane.  The pass can infer an output without checking every operand or shape.  A producer still supplies well-scoped and correctly typed operands, legal bounds and arities, and a valid output signature.  [Types pass](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/src/type_inference.rs#L179-L202) · [Backend architecture](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/zk_stdlib/src/lib.rs#L171-L209) · [Agda configuration theorem](../src/zkir-v4/Producer.agda)

### 3.3 Where a condition is checked

A circuit constraint applies to every assignment, including one supplied independently of preprocessing.  A VM check applies to the particular preimage being executed.  A producer obligation is a premise about the source or its intended use.  For example, the VM accepts `Assert(x)` only for native one, whereas the lowering constrains `x ≠ 0`.  If earlier instructions constrain `x` to be a bit, these conditions coincide.  A diagnostic that compares a computed cell with its known VM value during proving adds no such bit constraint.  [Assertion in the two passes](../../zkir/src/ir_vm.rs) · [Replay premises](#82-producer-obligations-and-faithfulness)

| Boundary | Example condition | Outcome when it fails |
| --- | --- | --- |
| Rust source loader | JSON has a supported major and minor version, and operands have a valid representation. | Loading returns an error before a preimage is supplied. |
| Rust validation shared by both passes | A prepared proof has a preceding binding with matching guard, and consumed accumulators and referenced keys satisfy §5. | The source fails validation independently of witness values. |
| Agda producer checker | Declared inputs and value results have fresh names, operands have supported types, and `Output` has the required placement. | `producer?` excludes the source from the producer theorems. |
| VM preprocessing | An active impact matches the next transcript fields, all streams finish together, and an enabled commitment matches the run. | `check` and `prove` can return a preprocessing error. |
| Circuit construction | Each instruction uses parameters supported by its chip.  RC1 supports requested comparison widths up to 252 bits. | The backend cannot construct the circuit with unsupported parameters. |
| Circuit satisfaction | The public and witness cells satisfy every emitted constraint, including the equality from `ConstrainEq`. | An assignment with unequal cells fails that constraint in the constructed circuit. |
| Ledger verification | The carried count matches the key, the outer proof verifies for the reconstructed instance, and every carried accumulator passes its pairing check. | The verifier rejects.  In particular, the pairing stage can reject after successful outer verification. |

Sections 4 and 5 give the per-instruction conditions.  [Producer checker](../src/zkir-v4/Producer.agda) · [Verifier interface](#6-proving-and-verification)

## 4. Instructions

The tables are in binary variant order.  Signatures name the JSON fields in payload order.  An operand field contains a variable reference or immediate, and its annotation gives the type of the resolved value.  A result field contains an identifier to bind, and its annotation gives the type of the value written there.  For example, `encode(input: T, outputs: [N])` takes one operand and an array of result names such as `["%lo", "%hi"]`.  Fields such as `bits`, `type` and `alignment` carry literal instruction parameters.  `N` is `Native`, `Bₙ` is `Bytes(n)`, `T` is a typed value, and brackets denote lists.  `Prime` means `Native` and the seven other prime-field types in [§2](#2-types-and-encodings).  `Point` ranges over the four point types, with `Base` and `Scalar` referring to the corresponding fields.  A native bit is an `N` restricted to `0, 1`.  Operand lookups, type mismatches, and arity mismatches fail unless an explicit off-circuit guard suppresses them.  A synthesis column may describe a constraint that becomes unsatisfiable on an invalid witness, or a structural error that prevents circuit construction, depending on whether the problem is in the value or the source.

The formal status for every row is an executable preprocessing rule and circuit contract.  The common value operations share a functional primitive.  Bit decomposition, assertion, selection, equality, aligned hashes, transcript reads, outputs and recursion have separate circuit rules.  Section 8.2 gives the hypotheses under which the two executions agree.  [Value operations](../src/zkir-v4/Operations.agda) · [Stateful instructions](../src/zkir-v4/Semantics.agda) · [Circuit dispatch](../src/zkir-v4/Circuit.agda)

### 4.1 Core instructions

| No. | JSON operation and signature | Preprocessing and rejection | Synthesis contract | Rust source |
| ---: | --- | --- | --- | --- |
| 0 | `encode(input: T, outputs: [N])` | Write the canonical encoding, with exactly one name per field.  Accumulators may be inspected this way without consumption. | Constrain the canonical field representation, including each accumulator point and unit scalar. | [Encode](../../zkir/src/ir_instructions/encode.rs) |
| 1 | `assert(cond: N)` | Require a native bit equal to 1. | Enforce that the operand is nonzero. | [Preprocess](../../zkir/src/ir_vm.rs#L438) · [Synthesis](../../zkir/src/ir_vm.rs#L1204) |
| 2 | `cond_select(bit: N, a: T, b: T, output: T)` | Require a native bit and identical types, including byte length.  Resolve both arms and select `a` for 1, `b` for 0. | Constrain the selector to be a bit and select on the supported types in [§4.3](#43-type-support). | [Selection](../../zkir/src/ir_instructions/select.rs) |
| 3 | `constrain_bits(val: N, bits: u32)` | Require `bits < 255` and ⟦val⟧ < 2ᵇⁱᵗˢ. | Decompose to at most 255 bits.  At width 255 the chip checks canonicality.  Wider decompositions exceed the chip bound. | [Preprocess](../../zkir/src/ir_vm.rs#L498) · [Synthesis](../../zkir/src/ir_vm.rs#L1218) |
| 4 | `constrain_eq(a: T, b: T)` | Require the same type and equal values. | Require equality on supported types, including componentwise equality of byte strings of identical length. | [Equality constraint](../../zkir/src/ir_instructions/constrain_eq.rs) |
| 5 | `constrain_to_boolean(val: N)` | Require a native bit. | Convert the cell to a bit, constraining its value. | [Preprocess](../../zkir/src/ir_vm.rs#L497) · [Synthesis](../../zkir/src/ir_vm.rs#L1233) |
| 6 | `copy(val: T, output: T)` | Bind the same value.  Reject `Accumulator`. | Reuse the assigned value.  Reject `Accumulator`. | [Preprocess](../../zkir/src/ir_vm.rs#L488) · [Synthesis](../../zkir/src/ir_vm.rs#L1239) |
| 7 | `impact(guard: N, inputs: [N])` | For 1, append the values, read and match that many public transcript inputs, and append `None` to the skip list.  For 0, append as many zeros, read no transcript fields or value operands, and append `Some(input count)`. | Convert the guard to a bit, resolve all operands, and expose each operand selected against zero. | [Preprocess](../../zkir/src/ir_vm.rs#L619) · [Synthesis](../../zkir/src/ir_vm.rs#L1249) |
| 8 | `ec_mul(a: Point, scalar: Scalar, output: Point)` | Multiply by a scalar of the same curve. | Constrain scalar multiplication on the point's curve. | [Curve multiplication](../../zkir/src/ir_instructions/ec_mul.rs) |
| 9 | `ec_mul_generator(scalar: Scalar, output: Point)` | Multiply the fixed generator of the scalar's curve. | Assign the generator as fixed and constrain scalar multiplication. | [Preprocess](../../zkir/src/ir_vm.rs#L671) · [Synthesis](../../zkir/src/ir_vm.rs#L1461) |
| 10 | `hash_to_curve(inputs: [N], output: JubjubPoint)` | Apply the pinned Midnight hash-to-Jubjub function. | Constrain its Poseidon-based hash-to-curve contract. | [Preprocess](../../zkir/src/ir_vm.rs#L656) · [Synthesis](../../zkir/src/ir_vm.rs#L1490) |
| 11 | `into_coordinates(point: Point, outputs: (Base, Base))` | Return affine `x, y`.  Reject a Weierstrass identity. | Extract affine coordinates and constrain a Weierstrass point to be nonidentity. | [Coordinates](../../zkir/src/ir_instructions/into_coordinates.rs) |
| 12 | `from_coordinates(inputs: (Base, Base), output: Point)` | Build a point from valid affine coordinates of the same field.  Check Edwards subgroup membership.  A Weierstrass identity has no affine representation here. | Constrain point construction from the two assigned coordinates using the curve chip. | [Point construction](../../zkir/src/ir_instructions/from_coordinates.rs) |
| 13 | `into_bytes32(input: Prime or Edwards Point, output: B₃₂)` † | Apply `ToBytes` and require exactly 32 bytes. | Constrain the same encoding and require width 32. | [Preprocess](../../zkir/src/ir_vm.rs#L702) · [Synthesis](../../zkir/src/ir_vm.rs#L1521) · [Byte encoding](../../zkir/src/ir_instructions/to_bytes.rs) |
| 14 | `from_bytes32(bytes: B₃₂, type: Prime or Edwards Point, output: type)` † | Require exactly 32 input bytes, then apply `FromBytes`. | Require width 32 and constrain the same reduction or point decoding. | [Preprocess](../../zkir/src/ir_vm.rs#L718) · [Synthesis](../../zkir/src/ir_vm.rs#L1542) · [Byte decoding](../../zkir/src/ir_instructions/from_bytes.rs) |
| 15 | `reverse_bytes(bytes: Bₙ, output: Bₙ)` † | Reverse bytes, using the same arm as `Reverse`. | Reorder existing byte cells. | [Preprocess](../../zkir/src/ir_vm.rs#L729) · [Synthesis](../../zkir/src/ir_vm.rs#L1554) |
| 16 | `bytes32_into_low_high(bytes: B₃₂, outputs: (N, N))` † | Return the first 31 bytes packed little-endian, then the last byte. | Convert the last byte to native and pack the other bytes through the native reduction helper with the last byte replaced by zero. | [Preprocess](../../zkir/src/ir_vm.rs#L799) · [Synthesis](../../zkir/src/ir_vm.rs#L1629) |
| 17 | `bytes32_from_low_high(inputs: (N, N), output: B₃₂)` † | Return the low operand as 31 little-endian bytes followed by the high byte.  Reject low ≥ 2²⁴⁸ or high ≥ 256. | The high operand has a byte range check.  The low operand is decomposed to bytes, with its 32nd byte constrained to zero. | [Preprocess](../../zkir/src/ir_vm.rs#L808) · [Synthesis](../../zkir/src/ir_vm.rs#L1638) |
| 18 | `div_mod_power_of_two(val: N, bits: u32, outputs: [N])` † | Require two outputs and `bits ≤ 248`.  Return quotient then remainder of ⟦val⟧ divided by 2ᵇⁱᵗˢ. | Split the canonical bit decomposition into low and high parts, and bind high then low.  The producer supplies the width restriction. | [Preprocess](../../zkir/src/ir_vm.rs#L501) · [Synthesis](../../zkir/src/ir_vm.rs#L1404) |
| 19 | `reconstitute_field(divisor: N, modulus: N, bits: u32, output: N)` † | For `b = bits`, require `1 ≤ b ≤ 248`, ⟦modulus⟧ < 2ᵇ, ⟦divisor⟧ < 2²⁵⁵⁻ᵇ, and ⟦divisor⟧·2ᵇ + ⟦modulus⟧ < the order of `F`.  Return that integer as a field element.  Zero bits fails the high-part bit bound. | Assign the result and split its canonical bits at `b`.  Require the low and high parts to equal the two operands.  This enforces the canonical upper bound and prevents field wraparound. | [Preprocess](../../zkir/src/ir_vm.rs#L518) · [Synthesis](../../zkir/src/ir_vm.rs#L1424) |
| 20 | `transient_hash(inputs: [N], output: N)` | Apply the pinned transient field hash to the ordered elements. | Constrain the Poseidon hash. | [Preprocess](../../zkir/src/ir_vm.rs#L574) · [Synthesis](../../zkir/src/ir_vm.rs#L1263) |
| 21 | `persistent_hash(alignment, inputs: [N], output: B₃₂)` | SHA-256 of the byte stream obtained under the alignment.  Reject a failed alignment parse. | Decode alignment-supported byte cells and constrain SHA-256. | [Preprocess](../../zkir/src/ir_vm.rs#L584) · [Synthesis](../../zkir/src/ir_vm.rs#L1273) |
| 22 | `keccak256(alignment, inputs: [N], output: B₃₂)` | Keccak-256 of the aligned bytes.  Reject a failed alignment parse. | Decode alignment-supported byte cells and constrain Keccak-256. | [Preprocess](../../zkir/src/ir_vm.rs#L589) · [Synthesis](../../zkir/src/ir_vm.rs#L1278) |
| 23 | `test_eq(a: T, b: T, output: N)` | Return a native bit indicating equality.  Supported same-kind byte strings of different lengths yield zero. | Convert the equality result to native.  Byte strings require identical lengths. | [Equality test](../../zkir/src/ir_instructions/eq.rs) |
| 24 | `add(a: T, b: T, output: T)` | Add two of the same prime-field type or two points of the same curve. | Constrain the field or group addition using the corresponding chip. | [Addition](../../zkir/src/ir_instructions/add.rs) |
| 25 | `mul(a: Prime, b: Prime, output: Prime)` | Multiply two elements of the same field. | Constrain multiplication in that field. | [Multiplication](../../zkir/src/ir_instructions/mul.rs) |
| 26 | `neg(a: T, output: T)` | Take the additive inverse for a field element or point, or complement a `Bool`. | Constrain the inverse for the appropriate group or field, or the Boolean complement. | [Negation](../../zkir/src/ir_instructions/neg.rs) |
| 27 | `inv(a: Prime, output: Prime)` | Compute the multiplicative inverse in the operand type.  Zero fails. | Enforce inversion through the field chip. | [Inversion](../../zkir/src/ir_instructions/inv.rs) |
| 28 | `not(a: N, output: N)` | Require a native bit and return its complement. | Constrain conversion to a bit and expose the complement as native. | [Preprocess](../../zkir/src/ir_vm.rs#L409) · [Synthesis](../../zkir/src/ir_vm.rs#L1337) |
| 29 | `less_than(a: N, b: N, bits: u32, output: N)` | Require `bits < 255` and both representatives below 2ᵇⁱᵗˢ.  Return a native bit for the unsigned comparison. | Use effective width `max(bits + bits mod 2, 4)`.  The RC1 gadget requires the effective width to be at most 253, so the largest supported request is 252 bits.  Exact replay requires the operands to fit the requested width.  [RC1 gadget bound](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/field/native/native_gadget.rs#L298-L315) | [Preprocess](../../zkir/src/ir_vm.rs#L560) · [Synthesis](../../zkir/src/ir_vm.rs#L1360) |
| 30 | `jubjub_scalar_from_native(native: N, output: JubjubScalar)` | Reduce the canonical integer modulo the Jubjub scalar order. | Constrain the same remainder using big-integer division and assign the Jubjub scalar. | [Reduction](../../zkir/src/ir_instructions/encode.rs#L273) · [Preprocess](../../zkir/src/ir_vm.rs#L569) · [Synthesis](../../zkir/src/ir_vm.rs#L1371) |
| 31 | `public_input(guard?: N, type: IrType, output: type)` | Read from `public_transcript_outputs` if active.  Otherwise use the typed default. | Assign the free typed value. | [Preprocess](../../zkir/src/ir_vm.rs#L449) · [Synthesis](../../zkir/src/ir_vm.rs#L1379) |
| 32 | `private_input(guard?: N, type: IrType, output: type)` | Read from `private_transcript` if active.  Otherwise use the typed default. | Assign the free typed value. | [Preprocess](../../zkir/src/ir_vm.rs#L468) · [Synthesis](../../zkir/src/ir_vm.rs#L1384) |
| 33 | `output(vals: [T])` | Check arity and exact types against the return signature, then append the typed values. | Check the same signature and save the values for optional commitment encoding. | [Preprocess](../../zkir/src/ir_vm.rs#L865) · [Synthesis](../../zkir/src/ir_vm.rs#L1706) |

† Deprecated in the pinned Rust source.  The runtime dispatch for `IntoBytes32` and `FromBytes32` uses the common byte conversion helpers and checks width 32, which admits the two Edwards point types.  `Bytes32FromLowHigh` has a documented native/native signature.  Some additional 32-byte encodable types can reach its shared helper through the low operand, and preprocessing also applies the shared helper to the high operand.  Synthesis explicitly requires a native high operand.  The tables use the documented native/native signature for correspondence.

### 4.2 Byte, Boolean and recursive instructions

| No. | JSON operation and signature | Preprocessing and rejection | Synthesis contract | Rust source |
| ---: | --- | --- | --- | --- |
| 34 | `slice(bytes: Bₙ, start: u32, len: u32, output: Bₗₑₙ)` | Select bytes `[start, start + len)`.  Require `len ≥ 1`, no endpoint overflow and an endpoint at most `n`. | Reference the selected cells in order. | [Preprocess](../../zkir/src/ir_vm.rs#L737) · [Synthesis](../../zkir/src/ir_vm.rs#L1562) |
| 35 | `nth(bytes: Bₙ, index: u32, output: Byte)` | Return the byte at the zero-based index.  Require `index < n`. | Reference the corresponding byte cell. | [Preprocess](../../zkir/src/ir_vm.rs#L822) · [Synthesis](../../zkir/src/ir_vm.rs#L1649) |
| 36 | `concat(inputs: [Byte or Bₙ], output: Bₘ)` | Concatenate in operand order, with a `Byte` contributing one byte.  Require `1 ≤ m ≤ 2²⁴` for the resulting length. | Concatenate the byte cell lists. | [Preprocess](../../zkir/src/ir_vm.rs#L834) · [Synthesis](../../zkir/src/ir_vm.rs#L1669) |
| 37 | `load_constant(type: IrType, encoding: [N], output: type)` | Decode the canonical typed encoding.  Reject an encoding of the wrong width or value. | Decode at synthesis and assign the value as fixed data. | [Preprocess](../../zkir/src/ir_vm.rs#L857) · [Synthesis](../../zkir/src/ir_vm.rs#L1696) · [Fixed assignment](../../zkir/src/ir_instructions/assign_constant.rs) |
| 38 | `sha512(alignment, inputs: [N], output: B₆₄)` | SHA-512 of the aligned bytes.  Reject a failed alignment parse. | Decode alignment-supported byte cells and constrain SHA-512. | [Preprocess](../../zkir/src/ir_vm.rs#L594) · [Synthesis](../../zkir/src/ir_vm.rs#L1283) |
| 39 | `and(inputs: [Bool], output: Bool)` | Require a nonempty list of typed Booleans and compute its conjunction. | Constrain the conjunction on assigned bits. | [Preprocess](../../zkir/src/ir_vm.rs#L413) · [Synthesis](../../zkir/src/ir_vm.rs#L1345) |
| 40 | `or(inputs: [Bool], output: Bool)` | Require a nonempty list of typed Booleans and compute its disjunction. | Constrain the disjunction on assigned bits. | [Preprocess](../../zkir/src/ir_vm.rs#L417) · [Synthesis](../../zkir/src/ir_vm.rs#L1350) |
| 41 | `xor(inputs: [Bool], output: Bool)` | Require a nonempty list of typed Booleans and return true for an odd number of true inputs. | Constrain exclusive-or on the assigned bits. | [Preprocess](../../zkir/src/ir_vm.rs#L421) · [Synthesis](../../zkir/src/ir_vm.rs#L1355) |
| 42 | `to_bytes(input: Prime or Point, output: B₃₂ or B₃₃)` | Apply the byte representation in [§2.2](#22-byte-conversion).  Output width is 33 for the Weierstrass points and 32 otherwise. | Constrain canonical field decomposition or point compression. | [Byte encoding](../../zkir/src/ir_instructions/to_bytes.rs) |
| 43 | `from_bytes(bytes: Bₙ, type: Prime or Point, output: type)` | Reduce to the specified prime field or decode a canonical compressed point, as in [§2.2](#22-byte-conversion). | Constrain reduction, or assign a typed point and assert that compressing it reproduces the bytes. | [Byte decoding](../../zkir/src/ir_instructions/from_bytes.rs) |
| 44 | `reverse(bytes: Bₙ, output: Bₙ)` | Reverse the byte order. | Reorder existing byte cells. | [Preprocess](../../zkir/src/ir_vm.rs#L729) · [Synthesis](../../zkir/src/ir_vm.rs#L1554) |
| 45 | `bytes_into_natives(bytes: Bₙ, outputs: [N])` | Pack bytes as in [§2.1](#21-typed-encoding).  Require ⌈n/31⌉ outputs. | Constrain the same packing, using direct conversion for a one-byte chunk. | [Preprocess](../../zkir/src/ir_vm.rs#L756) · [Synthesis](../../zkir/src/ir_vm.rs#L1589) · [Encode](../../zkir/src/ir_instructions/encode.rs) |
| 46 | `bytes_from_natives(inputs: [N], len: u32, output: Bₗₑₙ)` | Require `1 ≤ len ≤ 2²⁴`, exactly ⌈len/31⌉ operands and each integer below 256ʳ for its own chunk width `r`. | Decompose each operand into exactly its chunk width, enforcing its bound. | [Preprocess](../../zkir/src/ir_vm.rs#L777) · [Synthesis](../../zkir/src/ir_vm.rs#L1610) |
| 47 | `prepare_verification(guard: N, vk_hash: hex, instance: [N], proof: Identifier, output: Accumulator)` | With resolved operands and key, return the trivial accumulator for 0.  For 1, parse the key and prepare the inner verification, resolving fixed bases and collapsing the accumulator. | Parse the key, construct the verifier gadget, constrain the guard as a bit, scale by the guard, and collapse. | [Preparation](../../zkir/src/ir_instructions/prepare_verification.rs) |
| 48 | `inner_proof(guard: N, output: Identifier)` | Consume one byte blob.  Bind the blob for 1 and the empty blob for 0. | Bind the witness slot with a free byte witness.  The preparation instruction constrains the shared guard. | [VM](../../zkir/src/ir_vm.rs) |
| 49 | `accumulate(inputs: [Accumulator], output: Accumulator)` | With at least two operands, fold under the Poseidon-based accumulator contract, then collapse. | Require collapsed operands and constrain the same fold and collapse. | [Accumulation](../../zkir/src/ir_instructions/accumulate.rs) |
| 50 | `verify_accumulator(input: Accumulator)` | Append its encoded fields to the accumulator block. | Check the collapsed representation and expose its fields. | [Preprocess](../../zkir/src/ir_vm.rs#L921) · [Synthesis](../../zkir/src/ir_vm.rs#L1777) · [Accumulation](../../zkir/src/ir_instructions/accumulate.rs) |

### 4.3 Type support

Each entry gives the shared preprocessing and synthesis domain.  The last column records additional preprocessing behavior where their domains differ.  These restrictions apply regardless of whether an operand's current value would allow an operation to short-circuit.

| Operation | Common domain | Additional behavior |
| --- | --- | --- |
| `Encode` | All sixteen type constructors | — |
| `Copy` | Every type except `Accumulator` | — |
| `Add` | Matching prime-field values or matching points | — |
| `Mul`, `Inv` | Prime-field values, with matching types for multiplication | — |
| `Neg` | Prime-field values, points and `Bool` | — |
| `TestEq` | Matching prime-field values, matching points, `Bool`, `Byte`, or two `Bytes` of equal length | Preprocessing also compares unequal byte lengths and returns false. |
| `ConstrainEq` | Same supported pairs as `TestEq` | Preprocessing also handles equality of accumulators. |
| `CondSelect` | Matching prime-field values, matching points, `Bool` and `Byte` | Preprocessing also selects on same-length byte strings and accumulators. |
| `And`, `Or`, `Xor` | Nonempty lists of `Bool` | — |
| `Assert`, `Not`, guards and selectors | `Native` bits | `Assert` requires 1 off-circuit and constrains nonzero in-circuit.  Transcript-read guards are preprocessing bookkeeping. |
| `EcMul`, `EcMulGenerator` | All four curves, each with its own scalar type | — |
| Coordinate operations | All four curves, each with its own base type | Weierstrass identities cannot be converted to or from affine coordinates. |
| `ToBytes`, `FromBytes` | All prime fields and all four point types | The point length and compressed encoding rules apply in both passes. |
| `Slice`, `Nth`, `Reverse`, `BytesIntoNatives` | `Bytes(n)` | These operations require a byte string even where the type pass can infer a byte length for a `Byte`. |
| `Concat` | `Byte` and `Bytes(n)` in any order | Result must contain at least one byte. |

### 4.4 Aligned byte hashes

`PersistentHash`, `Keccak256`, and `Sha512` use an explicit ledger field-aligned binary (FAB) descriptor to translate native elements into the bytes to hash.  This differs from the typed byte packing in [§2.1](#21-typed-encoding).  Preprocessing parses the field list with `Alignment::parse_field_repr` and uses the value's FAB binary representation.  Synthesis implements field and byte atoms.  A field atom consumes one field and emits its little-endian bytes.  A byte atom emitting `n = 31q + r` bytes consumes an initial partial limb when `r > 0`, then `q` full limbs.  It emits the full limbs in reverse operand order, with each limb little-endian, then emits the partial limb in little-endian order.  Byte decomposition enforces each limb's specified width.  Both RC1 passes resolve every operand, then hash only the fields consumed by the descriptor.  For a single field atom with two native operands, the digest therefore depends only on the first.  [RC1 field parser](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/fab.rs#L337-L344) · [FAB synthesis](../../zkir/src/ir_vm.rs#L130) · [FAB preprocessing](../../zkir/src/ir_vm.rs#L588) · [Pinned FAB definitions](https://github.com/midnightntwrk/midnight-ledger/tree/eb784a9bba926cb71eaf199a99b3949cc2885a87/base-crypto/src/fab)

The Agda checker `producer?` requires the operands to match the descriptor exactly.  It counts one native operand per field atom and ⌈n/31⌉ per byte atom of length `n`, summing the widths of the individual atoms.  It rejects short and surplus operand lists, non-native operands, options and compression atoms.  The latter two forms fail in RC1 synthesis.  The correspondence proofs also require the preprocessing and circuit hash primitives to return the same digest on the resolved fields.  [Producer checker](../src/zkir-v4/Producer.agda) · [Checked arity examples](../src/zkir-v4/BoundaryExamples.agda)

For example, this JSON instruction hashes one 32-byte FAB atom.  Its first operand is the one-byte partial limb (`1f`).  Its second is the full 31-byte limb (`00` through `1e` in little-endian byte order).

```json
{
  "op": "persistent_hash",
  "alignment": [{"tag": "atom", "value": {"tag": "bytes", "length": 32}}],
  "inputs": ["0x1f", "0x000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e"],
  "output": "%digest"
}
```

The SHA-256 input, in hex, is `000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f`.  The full limb comes first in the byte stream and the partial limb comes last.  The resulting `Bytes(32)` digest is `630dcd2966c4336691125448bbb25b4ff412a49c732db2c8abc1b8581bd710dd`.  For the same byte string the typed encoding in §2.1 puts the full limb first in the *field vector*.  [FAB byte reconstruction](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/repr.rs#L133)

## 5. Fixed-key recursive verification

### 5.1 Source validation and witness slots

Before either pass, scan the instructions for proof bindings.  An `InnerProof` introduces a proof name that must be fresh in the proof store.  A `PrepareVerification` consumes a preceding binding, exactly once, and its guard must be the same parsed operand as that of the binding.  Two different variable names with equal runtime values do not satisfy this rule.  Equivalent spellings of a field immediate parse to the same operand.  For a variable guard, the separate producer check in §1 also requires a previously bound native value and single assignment.  The final set of pending proof bindings must be empty.  A proof name never supplies an ordinary operand value.

Independently index `inner_vks` by SHA-256 of the complete bytes in each entry.  A duplicate digest is rejected.  The digest in every preparation must occur in this map.  Every table entry must be referenced by at least one preparation, regardless of its guard, and multiple preparations can reference one key.  The bytes are from `MidnightVK<KZG>::write` in `SerdeFormat::Processed`.  The lookup performs the digest checks even for an inactive preparation.  The inactive off-circuit helper can return before parsing the blob, whereas synthesis always parses the key and constructs the gadget.  A key that is merely indexed by digest can therefore pass an inactive preprocessing run and fail synthesis.  [Binding and key validation](../../zkir/src/ir_instructions/prepare_verification.rs)

A processed inner key identifies the commitment scheme and contains the versioned architecture, circuit size parameter, declared public-input count and PLONK verifying key.  The source digest covers this entire byte string.  [Processed key reader and writer](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/zk_stdlib/src/interface.rs#L99-L169)

Each `InnerProof` consumes one slot of `inner_proofs` in instruction order.  A missing slot or any surplus slot rejects the preimage.  For the honest witness, preprocessing copies the active bytes into the proof store and witness slot, and stores the empty blob in both places for an inactive slot.  Synthesis takes the bytes of each supplied slot in order.  An independently supplied witness can therefore carry nonempty bytes in a disabled slot.  Exact replay (§8) requires that slot to contain the empty blob.  Without this convention, changing only the discarded inactive bytes leaves the processed witness unchanged.  [Proof witness consumption](../../zkir/src/ir_vm.rs#L915) · [Disabled-slot example](../src/zkir-v4/ReverseBoundaryExamples.agda) · [Witness tests](../../zkir/tests/inner_witnesses.rs)

### 5.2 Preparation, folding and exposure

For an active `PrepareVerification`, interpret the supplied blob using the inner Poseidon circuit transcript.  Public instances use one empty column and one column containing `instance`, with no committed instances.  The producer supplies the complete native-field vector expected by the inner verifying key, including any fields binding accumulators carried by that inner relation.  The resulting PLONK KZG opening equation is represented as two multiscalar multiplications.  Resolve fixed bases from the key and collapse to a single point with scalar one per side.  Synthesis assigns the key's circuit data and fixed bases, prepares the opening equation, and scales by the Boolean guard before collapsing.  A zero guard yields the collapsed pair `(G1 identity, G1 identity)`, with scalar one on each side.  To encode it, let `[a, b]` be the G1 base-field encoding of coordinate zero in §2.1.  Each side contributes `[a, b, a, b, 1, 1]`, ending with the identity flag and unit scalar.  The source still supplies the expected instance shape and a readable key.  [Preparation](../../zkir/src/ir_instructions/prepare_verification.rs) · [Recursive proof tests](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/tests/verify_proof_e2e.rs)

For an inner evaluation domain of size `n` with `b` blinding factors, a nonempty instance column must satisfy `length(instance) + b + 1 ≤ n`.  Active preprocessing checks this bound, and synthesis constrains it at either guard value.  ZKIR calls PLONK preparation directly.  Exact agreement with the key’s declared public-input count and consumption of every proof byte are checks of the standalone verifier (§6).  The direct-verification laws in §5.3 specify the agreement needed on the prepared key and instance.  [ZKIR preparation](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/src/ir_instructions/prepare_verification.rs#L60-L135) · [Native domain bound](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/proofs/src/plonk/verifier.rs#L156-L163) · [Gadget domain bound](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/verifier/verifier_gadget.rs#L397-L411)

The standalone verifier reads its public-input count from the processed key.  Agda treats those bytes as opaque.  For the chains and trees in §§5.4–5.6, a key-schema premise identifies that count with the width of the chosen child circuit.  The proofs show that each assembled child instance has that width.  [Public-instance width and key schema](../src/zkir-v4/Protocol.agda)

The accumulator lifecycle is a static use check on names.  Producing an accumulator makes it pending.  Producers are a declared `Accumulator` input, `PublicInput`, `PrivateInput` or `LoadConstant` of type `Accumulator`, a preparation, and a fold.  A fold consumes its inputs left to right before introducing its output.  An exposure consumes its single operand.  Each consuming operand must name a pending accumulator.  An accumulator name may be introduced only once, and the pending set must be empty after the walk.  `Encode` leaves the pending set unchanged, and `Output` also leaves it unchanged.  `Copy` cannot take an accumulator.  The source's single-assignment discipline also excludes rebinding these names through ordinary value instructions.

`Accumulate` hashes the concatenated public-input encodings of its ordered collapsed operands with the fixed-length Poseidon hash.  Let `r` be the resulting native field element and let `T` retain the low 128 bits of a canonical field representative.  The instruction weights operand `i`, starting at zero, by `T(rⁱ)`, where each power is computed in the native field before truncation.  It takes the weighted sum on each side and collapses the two resulting points to unit scalars.  Bilinearity gives a valid output equation whenever all inputs have valid equations.  [ZKIR fold](../../zkir/src/ir_instructions/accumulate.rs) · [Native fold](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/verifier/accumulator.rs#L191-L206) · [Circuit fold](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/verifier/accumulator.rs#L403-L428) · [Truncation](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/verifier/utils.rs#L113-L140) · [Poseidon hash](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/circuits/src/hash/poseidon/mod.rs#L131-L151)

`VerifyAccumulator` exposes one collapsed accumulator's encoded fields in instruction order for later verification.  Validation requires every produced accumulator to reach an exposure, directly or through folds.  For a nested relation with carried accumulators, the producer must explicitly bind their encoded fields into the inner instance and explicitly fold or expose the corresponding accumulator values.  Preparation by itself defers the inner proof's own opening equation.  [Accumulator lifecycle and folding](../../zkir/src/ir_instructions/accumulate.rs) · [Nested proof use](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/tests/verify_proof_e2e.rs)

**Accounting for every active preparation**.  Fix a producer source (§1) and the ledger key generated for it.  Assume the outer backend can extract a satisfying witness for the verified full instance and that accumulator encodings satisfy the codec laws.  From an accepted ledger proof, Agda recovers one circuit execution with the caller's statement and exactly the accumulators whose pairings the ledger checked.  In that execution either every active `PrepareVerification` yields a valid opening equation, or there is a particular `Accumulate` whose output passes its pairing and at least one of its actual inputs fails.  The result covers folds of any supported arity and any sequence of folds and separate exposures.  It applies to producer sources outside the VM replay fragment as well.  [Ledger accounting theorem](../src/zkir-v4/AccumulatorVerification.agda)

The proof follows a preparation's output name through the validated instruction sequence.  Single assignment keeps the same accumulator value under that name.  An exposure appends the value to the checked list.  A fold consumes it as an operand and introduces a fresh output whose obligation can be followed in turn.  The validator requires the pending list to be empty at the end.  Under the preparation laws and direct-verifier agreement for each active key and instance on the extracted execution (§5.3), validity of an active opening implies that a direct proof exists for the resolved inner key and the exact instance used at that instruction.  An inactive instruction establishes no inner claim.  A child proof that carries its own accumulators still requires the explicit binding and checks described above.  [Lifecycle of names](../src/zkir-v4/AccumulatorLifecycle.agda) · [Validity along a circuit execution](../src/zkir-v4/AccumulatorObligations.agda)

**Computational folding assumption**.  Fix the verifier parameters.  In the bad-fold game, an algorithm outputs an ordered tuple of collapsed prime-order accumulators of the arity under consideration.  It wins if at least one input fails its pairing and the fold computed by the pinned algorithm passes.  The concrete assumption bounds the success probability of feasible algorithms in this game for the pinned fixed-length Poseidon hash.  To transfer such a bound to recursive proof acceptance, assume the circuit and verifier implement the stated primitive laws and the reduction can efficiently extract a satisfying execution on the full instance at each visited proof and recover an accepted child proof for the exact key and instance when descending.  The probability of accepting a false claim is then bounded by the reduction's bad-fold game success probability plus the probability that this extraction and recovery fails during the descent.  Agda gives the execution-or-bad-fold implication under its stated hypotheses.  A numerical bound for the production Poseidon fold and the costs and failure probabilities of extraction and recovery remain external to the Agda proof.  [Ledger reduction](../src/zkir-v4/AccumulatorVerification.agda) · [Recursive descent](../src/zkir-v4/SequentialVerification.agda)

For a binary fold, one can bound this game in an ideal model where a fresh ordered encoding gives an independent uniform field element, even given the algorithm's prior observations.  Write `p` for the native field order, and write the two input pairing residuals as exponents `d₀, d₁` of a generator of the order-`p` target group.  The injective tuple encoding fixes both operands before the reply, so the two exponents are fixed, and at least one is nonzero for a tuple with an invalid input.  The fold passes precisely when `d₀ + T(r)d₁ = 0` in the field.  If `d₁ = 0`, this is impossible.  Otherwise at most one truncated value works, with probability at most `⌈p/2¹²⁸⌉/p` for a fresh query.  For at most `q` distinct queries, including the evaluation of the final tuple if it was unqueried, the union bound is `min(1, q · ⌈p/2¹²⁸⌉/p)`.  For a recursive application, `q` includes the prover's search and any oracle queries made in extraction and recovery.  This idealized estimate requires the fresh uniform reply assumption for the entire experiment.  Higher arities require a bound for the zero set of the sum of exponents weighted by the actual truncated coefficients `T(rⁱ)`.  [Pairing check](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/proofs/src/poly/kzg/msm.rs#L281-L299)

### 5.3 Checking two proofs separately or together

Consider two fixed inner keys `K₁, K₂`, each for a relation with one native public field and no carried accumulators.  The keys may coincide.  Agda proves that both wrappers pass the source validator with a single shared key entry or with two entries having distinct SHA-256 digests.  For field values `x, y`, the claim to preserve is “there is a proof accepted by `K₁` for `[x]`, and there is a proof accepted by `K₂` for `[y]`.”  Direct verification here uses the inner Poseidon transcript and the same KZG parameters as preparation.  The ledger uses the outer Blake2b transcript when it checks a wrapper proof.  [Preparation](../../zkir/src/ir_instructions/prepare_verification.rs) · [Ledger interface](#6-proving-and-verification)

The Agda development constructs two IR sources.  Both declare native inputs `%x, %y`, publish them in one unconditional impact, consume two proof slots, and prepare one proof against each fixed key.  The first preparation takes `[%x]` and the second takes `[%y]`.  The same two operands supply the public statement fields immediately following the binding field.  Both guards are literal one, and communications commitment is disabled.  The wrappers differ only in their final instructions.

| Wrapper | Final instructions | Carried by the proof | External statement |
| --- | --- | --- | --- |
| Separate exposure | Expose each prepared accumulator. | `[a₁, a₂]` | `[binding, x, y]` |
| Folded exposure | Fold the ordered pair and expose its result. | `[fold(a₁, a₂)]` | `[binding, x, y]` |

**Completeness**.  If both direct proofs verify, an accepted proof exists for either wrapper for the same binding field, `x` and `y`.  This assumes a validated wrapper, the specified keys resolving and parsing, agreement of native and circuit preparation on supported inputs, correctness of direct verification via preparation and pairing, and completeness of the outer backend.  Folded exposure additionally needs a successful, valid fold for a pair of valid accumulators.  The proof constructs a satisfying witness of the actual instruction sequence for each case.  [Wrapper sources and completeness](../src/zkir-v4/RecursiveVerification.agda)

**Soundness**.  Acceptance of the separate wrapper implies that both direct proofs exist for the caller’s `x, y`.  This uses extraction under the wrapper key on the full public instance, the canonical codec laws, and agreement of the circuit and native preparation for each resolved, readable child key.  For each key on its one-field child instance, the direct-verifier law says that a prepared opening with a valid pairing implies the existence of a directly accepted proof.  The proof follows the two slots through preparation, then uses the key's exposure count and the injective accumulator encoding to identify the values checked by the ledger.  For the folded wrapper, Agda recovers both direct proofs or exhibits a bad fold of the two prepared accumulators.  The binary bad-fold game in §5.2 states the remaining computational assumption.  [Soundness and conversions between wrappers](../src/zkir-v4/RecursiveVerification.agda)

The conversion theorems preserve the external statement across the two wrapper keys.  The separate full instance has 24 accumulator fields before the statement, and the folded one has 12.  Their shared claim is a conjunction about `x` and `y`.  A claim that the second computation consumes the first computation's output also needs a constraint linking those values.

**Nested and guarded proofs**.  A Poseidon-transcript child proof can already carry accumulators `A`.  For a valid child proof, prepare its raw bytes on `encode(A) ++ child_statement`, where `encode(A)` concatenates the encodings in order.  This yields one new opening equation.  A parent must bind the child key's count, use those same carried values in the child instance, and discharge the new equation **and** all the equations in `A`.  Under the direct-verifier and chip laws for that full instance, these checks imply that a directly accepted child proof exists with the same carried values and statement.  The byte-preserving theorem assumes `ExactAt` for the supplied bytes and instance.  This law says that successful active preparation of those bytes with a valid pairing implies that the standalone verifier accepts those very bytes.  Applying it to RC1 requires justifying the standalone verifier’s instance-length and transcript-consumption checks.  The one-level theorem is parameterized by the child statement.  For an inactive compatible preparation with a readable key, the valid trivial accumulator discharges the skipped check.  That branch establishes no inner statement.  [Nested and disabled cases](../src/zkir-v4/RecursiveVerification.agda)

### 5.4 Proving a sequence of exactly `n` transitions

Fix an application program, an initialization predicate, a transition relation and a maximum depth.  The caller chooses the expected keys and supplies a public claim identifying the context, initial state, final state and step count.  The program can be fixed by the key.  The claim is that an execution connects the two states in **exactly the claimed number of transitions**.  For the counter below, Agda recovers that execution or identifies a bad fold.  A transition may return to the same state.

The base circuit must establish that the claimed start is an allowed initial state and that the finish equals the start.  A step circuit for count `n + 1` must prepare a child proof for count `n` under the expected predecessor key, preserve the program, context and start, and enforce one valid transition from the child's finish to its own finish.  It must bind the child's full instance and account for both its opening equation and its carried accumulators (§5.3).  Each circuit must bind the claim to its public fields with an unambiguous encoding.  For a predecessor at depth `n`, the verifier-agreement premise applies to its carried values and the encoded claim for that program, context, start and predecessor finish.  The proof uses the carried count and the child key’s schema to establish the instance length.  Given these facts, sound preparation and discharge of the pairing obligations, induction on the count gives the execution.  The induction can use any directly accepted child proof for the same instance.  [General sequential soundness theorem](../src/zkir-v4/SequentialVerification.agda)

For a concrete instance, consider a native-field counter initialized to its context value `c`.  Its transition adds one in the native field.  The statement is `[0, c, start, finish]` followed by exactly `n` zero fields.  For example, at context 42 the two-step claim is `[0, 42, 42, 44, 0, 0]`.  The length of the suffix after the first four fields encodes the count even when the state wraps around the field.

Each depth has a fixed circuit.  The depth-zero circuit publishes the same value for context, start and finish.  At positive depth the circuit publishes the result of adding one to its predecessor's finish and supplies that same predecessor value to an unconditional preparation.  The first step exposes the child's opening.  Subsequent steps encode the child’s single carried accumulator into its instance, fold it with the opening, and expose the result.  A child at depth zero takes four public fields.  At depth `n > 0` it takes `16 + n` fields, comprising twelve for its carry, four claim fields and `n` count markers.  [Counter sources and circuit observations](../src/zkir-v4/SequentialSource.agda)

For this family, `execution-or-bad-fold` proves that ledger acceptance gives either an execution of the claimed length or a path from the supplied proof to a step where two accumulators fold to a valid output while at least one input fails.  The path starts at the layer extracted from the accepted root.  Each descent records an accepted predecessor proof for the carried values and statement used by its parent.  The terminal layer identifies the actual fold, and `reached-level` bounds its level by the requested depth `n`.  This result assumes witness extraction for the circuits behind the selected keys, the codec laws, and agreement between preparation and direct verification for the inner keys.  `counter-sound` is the corollary under `PairSound`, the universal deterministic implication that a valid binary fold has two valid inputs.  It gives `start = c` and `finish` equal to the result of exactly `n` increments from `start`.  For a computational interpretation, the reduction in §5.2 visits at most one root and `n` inner proofs, with binary folds at levels two through `n`.  The extraction and recovery failure term covers the whole descent, and the fold game counts trial queries even for tuples absent from the extracted execution.  The caller authenticates the key for its requested depth within the configured limit.  Intermediate proofs use the inner Poseidon transcript and the ledger checks the root with Blake2b.  [Counter soundness and hypotheses](../src/zkir-v4/SequentialExample.agda)

**Completeness for the counter**.  For every context `c` and depth `n` within the limit, `counter-complete` constructs an accepted ledger proof with start `c` and finish equal to `n` native-field increments of `c`.  The base circuit publishes `[0, c, c, c]` and carries no accumulator.  Each successor uses a Poseidon proof of its predecessor on the predecessor's full instance.  It constructs the successor witness with the resulting opening and, from depth two onward, the child's carried accumulator.  The proof assumes that accepted Poseidon proofs prepare to valid openings under the pinned keys, circuit preparation agrees on these inputs, and folding two valid inputs succeeds with a valid result.  Backend completeness is required for the intermediate Poseidon circuits and the final Blake2b circuit.  [Witness construction](../src/zkir-v4/SequentialWitness.agda) · [Sequential completeness](../src/zkir-v4/SequentialCompleteness.agda)

The Rust conformance test uses the three circuits above.  At depth one it supplies the base proof's opening as the twelve-field prefix before `[0, 42, 42, 43, 0]`.  At depth two it checks the prefix against the fold of the depth-one opening and the base opening, in that order.  It passes the six-field statement to the ledger verifier and checks rejection after changing the context, either endpoint, the step count, or the number of carried accumulators.  [Depth-two counter test](../../zkir/src/sequential_counter.rs)

### 5.5 Proving a tree of application claims

A parent can require any finite list of child claims.  The application specifies which lists justify each parent.  For example, a rule for a computation from `x` to `z` can require children for `x` to `y` and `y` to `z`, under the same program and context.  The parent circuit must enforce the shared intermediate state `y`.  Only the root claim needs to be known to the caller.  The child claims and their order can be recovered from a satisfying witness.  A leaf must satisfy an application rule with no children.  [Claims, rules and derivations](../src/zkir-v4/ProofTree.agda)

**Soundness**.  The application proves what one execution of each producer source establishes for its public statement.  It identifies a rule and, for every child that rule requires, an active preparation in the execution under the expected child key.  The prepared fields must equal `encode(child_carried) ++ child_statement`, and the number of carried accumulators must match the child's exposure count.  Each carried value must also occur as an input to an executed fold or as an exposed value in the parent.  In a checked example with two children, the parent folds one child's carried accumulator with both proof openings and exposes the other child's accumulator separately.  A second example proves that exposing just the opening cannot discharge a different accumulator carried by the child.  [Child links](../src/zkir-v4/TreeTrace.agda) · [Both examples](../src/zkir-v4/TreeLinkExamples.agda)

Assume extraction for the expected root and inner keys, the codec and preparation laws, and a key schema for each required child.  Along each child edge the proof derives the exact full-instance length from the exposure count and the child’s statement.  It needs agreement with direct verification on that key and instance.  Each required child must be smaller in an order that rules out infinite descent.  A decreasing depth suffices.  An accepted root then yields either a finite derivation of the caller's claim or a path to a particular bad fold.  The path follows required children on their exact full instances.  At its end, an executed fold has a valid output and an actual input that fails its pairing.  Excluding this event gives the derivation.  Each recovered child has some accepted proof for its instance.  Equal child claims can share evidence, so an application that requires distinct events must bind their identities.  [Tree soundness](../src/zkir-v4/TreeSoundness.agda)

**Completeness**.  In the other direction, the application gives a construction for each rule it uses.  Given accepted proofs for the rule's ordered children, it builds a satisfying parent witness that publishes the parent statement and carries only valid accumulators.  With complete proving backends for the constructed nodes, every finite derivation yields an accepted proof for its root statement.  Intermediate nodes use the inner verifier and the root uses the ledger verifier.  A prover may also supply already accepted inner proofs for entire subtrees.  Those subtrees require no witness reconstruction.  [Tree completeness](../src/zkir-v4/TreeCompleteness.agda)

### 5.6 Splitting and joining counter segments

A segment claims that exactly `n` native-field increments take `x` to `z` in application context `c`.  Its public statement is `[0, c, x, z]` followed by `n` zero fields.  A segment may start at any field value.  To verify an initialized counter, the caller supplies `c` for both context and start at the root.  For example, the statement `[0, 42, 42, 45, 0, 0, 0]` can be proved by joining two increments from 42 to 44 with one from 44 to 45.  The join uses 44 as a private input shared by both preparations.  [Segment claims](../src/zkir-v4/SegmentClaims.agda)

The expected key fixes the shape of the circuit.  An idle leaf publishes its start as its finish and counts zero steps.  A tick leaf adds one in the native field and counts one step.  Both expose one accumulator, for which the honest witness uses the trivial accumulator.  A join counts the sum of its children's steps.  Each preparation uses the expected child key and the full child instance, including the encoding of its carried accumulator.  For a child of `n` steps this gives `16 + n` fields at every shape, even an idle leaf.  The left finish and the right start use the same operand.  The join folds the left opening, left carry, right opening and right carry in that order and exposes the single result.  Equal child keys share a table entry.  Distinct child keys in one table must have distinct digests.  [Circuit sources](../src/zkir-v4/SegmentSource.agda) · [Validation and key lookup](../src/zkir-v4/SegmentStatic.agda)

**Join soundness**.  From an accepted join, Agda recovers a midpoint and an accepted inner proof for each of the two corresponding segments, or identifies a bad fold on the accepted execution.  Recursing through the children gives an execution with the published endpoints and exact step count or a path to a bad fold.  The proof derives the common midpoint, both active preparations, their public fields and their carried values from the circuit instructions.  It assumes the codec laws, agreement between preparation and direct verification, and witness extraction under the selected keys.  The join's computational interpretation uses the four-input bad-fold game in §5.2.  [Join observation](../src/zkir-v4/SegmentJoinObserve.agda) · [Soundness](../src/zkir-v4/SegmentSoundness.agda)

**Split completeness**.  For a split into `i` and `j` steps, an honest execution of length `i + j` determines the midpoint after step `i`.  The two segments can be proved independently and their accepted inner proofs used to construct the ledger proof.  Either side may have length zero.  The construction uses the concrete witnesses for the leaves and joins.  It assumes readable inner keys, agreement of the preparation and verification primitives, validity of the trivial accumulator, a successful valid fold for four valid inputs, and completeness of the inner and ledger backends.  Both child shapes and the join must fit within the configured height limit.  [Leaf witnesses](../src/zkir-v4/SegmentLeaf.agda) · [Join witness](../src/zkir-v4/SegmentJoinWitness.agda) · [Split completeness](../src/zkir-v4/SegmentCompleteness.agda)

**Regrouping**.  For three consecutive segments `A`, `B` and `C`, the shapes `((A,B),C)` and `(A,(B,C))` have the same external statement.  From a proof accepted under one shape's ledger key, the soundness and completeness theorems give a proof under the other key or identify a bad fold in the input proof tree.  When bad folds are excluded and both shapes fit the height limit, existence of an accepted proof is equivalent in both directions.  Each grouping produces its own proof bytes and carried accumulator.  [Regrouping theorems](../src/zkir-v4/SegmentRegroup.agda)

## 6. Proving and verification

Let `A = [a₀, …, aₖ₋₁]` be the accumulators in exposure order, and let `I` be the impact fields in instruction and operand order, including the zeros for inactive impacts.  The interface uses the following vectors.

| Value | Layout |
| --- | --- |
| Returned statement | `[binding_input] ++ [commitment if enabled] ++ I` |
| Full circuit public input | `encode(a₀) ++ … ++ encode(aₖ₋₁) ++ returned_statement` |
| Returned skip list | One entry per `Impact`, in instruction order.  `None` for active impacts and `Some(operand count)` for inactive impacts. |
| Returned proof | `Proof { bytes, accumulators: A }`, with `bytes` the outer proof bytes |

The accumulator block occupies `12k` field elements.  Exposure can occur before, between, or after impacts, and the accumulator block always precedes the entire statement.  Declared typed returns and the inner proof witness blobs have no separate fields in this interface.  To include information from a return in the external statement, the producer must also expose it through an impact or the communications commitment according to the intended statement.  Skips are proving and checking metadata.  They are not inputs to ledger verification.

Key generation binds `k`, the number of `VerifyAccumulator` instructions, in the ledger verifier key.  Proving runs preprocessing, generates the outer KZG PLONK proof over the full circuit input using the ledger Blake2b transcript, decodes the completed leading block into `A`, and returns the split above.  The ledger verifier checks the accumulator count against the key, reconstructs the full input from the proof's accumulators and caller-supplied statement, verifies the outer proof bytes, then checks the deferred KZG pairing equation for every carried accumulator against the verifier parameters.  The outer verifier requires the reconstructed vector to have exactly the public-input count recorded in the backend key and to fit the usable domain rows.  It also requires complete consumption of the outer proof bytes.  A proof can pass outer verification and fail a deferred pairing.  [Proving and key generation](../../zkir/src/ir.rs#L97) · [Ledger verification](https://github.com/midnightntwrk/midnight-ledger/blob/eb784a9bba926cb71eaf199a99b3949cc2885a87/transient-crypto/src/proofs.rs#L879-L914) · [Standalone verifier](https://github.com/midnightntwrk/midnight-zk/blob/4575056ad96a2e70321f0bd8577dea2cd8d8b2e3/zk_stdlib/src/interface.rs#L619-L646)

## 7. Examples

The Rust reference tests load the JSON for all four examples.  For §7.1, `byte_packing` runs preprocessing and checks the packed value, public fields and skip list.  In Agda the same source belongs to the static replay fragment, and `PackingRoundTrip.round-trip` applies both correspondence theorems to its successful run.  [Worked Agda proof](../src/zkir-v4/CorrespondenceExamples.agda)

For §§7.2 and 7.3, the release test `verify_reference_proofs` generates an outer key pair for each source, proves each at both guard values, compares the returned statement and verifies the result with the ledger verifier.  For these two sources, Agda proves that every satisfying circuit witness has a successful VM preimage with the same statement and carried accumulator.  The preparation constrains the declared `%guard` to zero or one.  At zero the VM preimage uses an empty slot, even if the circuit witness supplied other bytes there.  The proof also recovers the impact inputs and skips for the selected branch.  It uses the backward preparation contract in §8.2.  [Guarded replay theorems](../src/zkir-v4/GuardedExamples.agda) · [Executable examples](../../zkir/src/spec_examples.rs) · [Reproduction commands](zkir-v4-plan.md)

### 7.1 Byte packing at 32 bytes

This source assembles 31 zero bytes followed by byte 42.  It returns the byte string and exposes its two packed fields.  The raw inputs and the two typed-read transcripts are empty.  Use binding input 99, public transcript inputs `[0, 42]`, and no commitment or proof witnesses.  The return is `Bytes(32)`, the full circuit input and external statement each equal `[99, 0, 42]`, and the skip list is `[None]`.

```json
{
  "version": {"major": 4, "minor": 0},
  "inputs": [],
  "outputs": ["Bytes<32>"],
  "do_communications_commitment": false,
  "instructions": [
    {"op": "load_constant", "type": "Bytes<31>", "encoding": ["0x00"], "output": "%prefix"},
    {"op": "load_constant", "type": "Byte", "encoding": ["0x2a"], "output": "%last"},
    {"op": "concat", "inputs": ["%prefix", "%last"], "output": "%bytes"},
    {"op": "bytes_into_natives", "bytes": "%bytes", "outputs": ["%lo", "%hi"]},
    {"op": "bytes_from_natives", "inputs": ["%lo", "%hi"], "len": 32, "output": "%roundtrip"},
    {"op": "constrain_eq", "a": "%bytes", "b": "%roundtrip"},
    {"op": "impact", "guard": "0x01", "inputs": ["%lo", "%hi"]},
    {"op": "output", "vals": ["%roundtrip"]}
  ]
}
```

For this length `BytesFromNatives` accepts `[2²⁴⁸−1, 255]` and rejects `[2²⁴⁸, 0]` and `[0, 256]`.  A valid `Bytes(31)` instead uses precisely one limb.  Calling `TestEq` on `%prefix` and `%bytes` would return zero in preprocessing and fail synthesis, because the two byte lengths differ.  [Byte conformance tests](../../zkir/tests/typed_outputs/conformance.rs) · [Rust VM](../../zkir/src/ir_vm.rs)

### 7.2 Fixed key, one preparation

Generate a key and a Poseidon-transcript proof of the instance `[123]` using the `SingleScalarRelation` fixture.  Let `B` be its processed verifying-key bytes and `p` its proof bytes.  The two substitutions for the source below are the byte array `B` in place of `[0]` and the hex SHA-256 digest of `B` in place of the digest of `[0]`.  The one-byte placeholder key is valid JSON and needs to be replaced before synthesis.  `0x7b` denotes the native element 123.  This is the same procedure for both guard values and uses one outer key pair.  [Scalar proof fixture](../../zkir/tests/common/verify_proof.rs#L265-L287) · [Shared-guard verification test](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/tests/verify_proof_e2e.rs#L355)

```json
{
  "version": {"major": 4, "minor": 0},
  "inputs": [{"name": "%guard", "type": "Scalar<BLS12-381>"}],
  "outputs": [],
  "do_communications_commitment": false,
  "inner_vks": [[0]],
  "instructions": [
    {"op": "inner_proof", "guard": "%guard", "output": "%p"},
    {"op": "prepare_verification", "guard": "%guard", "vk_hash": "0x6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
     "instance": ["0x7b"], "proof": "%p", "output": "%a"},
    {"op": "verify_accumulator", "input": "%a"}
  ]
}
```

Use binding input 99, the single native guard as the raw input, and empty field transcripts.  With guard one, provide `Direct(p)` and expect the prepared accumulator `a`.  With guard zero, provide one slot such as `Direct([])` and expect the trivial accumulator.  In both cases the statement is `[99]`, the skip list is empty, and the proof carries one accumulator.  The full circuit input is that accumulator's twelve fields followed by 99.  Either guard value requires exactly one proof slot and the same key table.  Appending a spare slot, omitting the slot, omitting or duplicating the key, adding an unused key, changing only one guard operand, or deleting or duplicating the exposure violates the corresponding validation or exhaustion rule.  [Witness checks](../../zkir/tests/inner_witnesses.rs) · [Key and accumulator checks](../../zkir/tests/verify_proof.rs)

### 7.3 Fold with interleaved impacts

Use the same processed key and digest substitutions and the same instance fixture.  Both preparations refer to one table entry.  The first preparation is active and uses `Direct(p)`.  The second receives `Direct(p)` when `%guard = 1` and `Direct([])` when `%guard = 0`.  Both proof slots are always present.  Use binding input 99, no commitment, the guard as the single declared input, and empty typed-read transcripts.

```json
{
  "version": {"major": 4, "minor": 0},
  "inputs": [{"name": "%guard", "type": "Scalar<BLS12-381>"}],
  "outputs": [],
  "do_communications_commitment": false,
  "inner_vks": [[0]],
  "instructions": [
    {"op": "inner_proof", "guard": "0x01", "output": "%p"},
    {"op": "prepare_verification", "guard": "0x01", "vk_hash": "0x6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
     "instance": ["0x7b"], "proof": "%p", "output": "%a"},
    {"op": "impact", "guard": "0x01", "inputs": ["0x2a"]},
    {"op": "inner_proof", "guard": "%guard", "output": "%q"},
    {"op": "prepare_verification", "guard": "%guard", "vk_hash": "0x6e340b9cffb37a989ca544e6bb780a2c78901d3fb33738768511a30617afa01d",
     "instance": ["0x7b"], "proof": "%q", "output": "%b"},
    {"op": "accumulate", "inputs": ["%a", "%b"], "output": "%c"},
    {"op": "verify_accumulator", "input": "%c"},
    {"op": "impact", "guard": "%guard", "inputs": ["0x07", "0x08"]}
  ]
}
```

Let `a` be the active preparation and `t` the trivial accumulator.  For guard one, public transcript inputs are `[42, 7, 8]`, the statement is `[99, 42, 7, 8]`, and the skip list is `[None, None]`.  The proof is `{bytes: outer_proof_bytes, accumulators: [fold(a, a)]}`.  For guard zero, public transcript inputs are `[42]`, the statement is `[99, 42, 0, 0]`, and the skip list is `[None, Some(2)]`.  The proof is `{bytes: outer_proof_bytes, accumulators: [fold(a, t)]}`.  The fold is ordered and each proof has one exposure despite the two preparations.  For either guard the 16-field circuit input is the encoding of the fold followed by the four statement fields.  [Folding](../../zkir/src/ir_instructions/accumulate.rs) · [Impact ordering test](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/tests/verify_proof_e2e.rs#L396)

### 7.4 A hash preimage and its public nullifier

A contract reads two private native fields `x, r` and a native field `h` from the public transcript.  It checks `H(x, r) = h` and publishes the nullifier `n = H(x)`, a public identifier that a caller can use to detect repeat use of the same secret.  Here `H` is the Poseidon hash used by `TransientHash`.  The question for a verifier is whether the public statement binds that nullifier to a particular digest `h`.

```json
{
  "version": {"major": 4, "minor": 0},
  "inputs": [], "outputs": ["Scalar<BLS12-381>"],
  "do_communications_commitment": false,
  "instructions": [
    {"op": "private_input", "type": "Scalar<BLS12-381>", "output": "%x"},
    {"op": "private_input", "type": "Scalar<BLS12-381>", "output": "%r"},
    {"op": "transient_hash", "inputs": ["%x", "%r"], "output": "%hc"},
    {"op": "public_input", "type": "Scalar<BLS12-381>", "output": "%h"},
    {"op": "constrain_eq", "a": "%hc", "b": "%h"},
    {"op": "transient_hash", "inputs": ["%x"], "output": "%n"},
    {"op": "impact", "guard": "0x01", "inputs": ["%n"]},
    {"op": "output", "vals": ["%n"]}
  ]
}
```

Take binding input `b`, private transcript `[x, r]`, public transcript outputs `[h]`, and public transcript inputs `[n]`.  The declared input vector and inner-proof stream are empty.  The run starts with statement `[b]`.

| Instruction | VM action | Circuit relation |
| --- | --- | --- |
| 1. First private read | Consume `x` and bind `%x`. | Assign a native witness cell. |
| 2. Second private read | Consume `r` and bind `%r`. | Assign a native witness cell. |
| 3. First hash | Bind `%hc = H(x, r)`. | Constrain the hash result to the two input cells. |
| 4. Public read | Consume `h` and bind `%h`. | Assign a native witness cell. |
| 5. Equality | Require `%hc = %h`. | Constrain the two cells to be equal. |
| 6. Second hash | Bind `%n = H(x)`. | Constrain the nullifier cell to the hash of `%x`. |
| 7. Impact | Match and consume `n`, append it to the statement, and record `None` in the skip list. | The fixed guard is one, so the selected public field equals `%n`. |
| 8. Output | Append the native `%n` to the declared returns. | Check its type.  With commitment disabled the return adds no public field. |

All streams are exhausted.  The full instance and external statement are both `[b, n]`, and the proof carries no accumulators.  Given these public fields, the circuit requires witnesses `x, r, h` such that `n = H(x)` and `h = H(x, r)`.  Since `h` is existential, this proves knowledge of a preimage of `n` under the backend knowledge assumption.  Binding the proof to a particular caller-supplied digest would require exposing `h` as well, for example in the same `Impact`.  The return value alone has no such effect.  The executable example uses `x = 7`, `r = 11` and `b = 99`.  [Example test](../../zkir/src/spec_examples.rs)

## 8. Correspondence and trust assumptions

Fix a source `S`.  Write `run(S, P) = Σ` for successful preprocessing of preimage `P`, `stmt(Σ)` for the external statement, and `π(Σ)` for the full instance including the accumulator prefix.  The labels P1–P10 identify the corresponding questions in the v3 specification.  The hypotheses and conclusions below are for IR 4.0.  For example, §7.2 has statement `[99]` for either guard value, while the guard selects which accumulator to expose.  [Two execution passes](#3-two-execution-passes) · [Verification interface](#6-proving-and-verification)

### 8.1 Operational properties

| Property | Statement and proof status |
| --- | --- |
| P1. Consumption | If `run(S, P) = Σ`, all four streams are exhausted, and any enabled commitment check passed.  `preprocess-inversion` recovers those facts and the trace of executed instructions. |
| P2. Growth | On every successful VM trace the external statement and accumulator block each grow by appending fields.  This is a prefix property of each block individually.  A later exposure inserts fields before the statement in the assembled instance.  On a typed producer trace, previously bound values keep their values.  The proofs are `run-prefixes` and `trace-extends`.  For an accepted run, `preprocess-exposure` counts carried accumulators and `preprocess-full-inputs` gives the assembled instance. |
| P3. Determinism | For fixed `S` and `P`, any two successful final states are equal.  `interprets-deterministically` proves this for the partial interpreter. |
| P4. Store typing | At each step of a successful producer trace, every name in the inferred type environment is bound to a value of the inferred type.  `trace-store` constructs the typed trace and records the writes at each step.  V3 also states that every name in memory belongs to the environment.  That exact-domain corollary is not stated as a v4 theorem. |

[Interpreter properties](../src/zkir-v4/SemanticsProperties.agda) · [Typed traces and preservation](../src/zkir-v4/ProducerMemory.agda) · [Store invariant](../src/zkir-v4/ProducerStore.agda)

### 8.2 Producer obligations and faithfulness

**P5, from a run to a witness**.  For a producer source, if `run(S, P) = Σ`, the forward preparation contract holds and each primitive call meets its forward conditions, then `C(S; π(Σ), honest-witness(P, Σ))` holds in the model.  The Agda theorem is `producer-forward`.  For the RC1 comparison gadget, `forward-with-comparison-cap` additionally checks that every requested `LessThan` width rounds to at most 253.  Agda proves that this is equivalent to requesting at most 252 bits.  Acceptance by `producer?` supplies single assignment, scope, typing, bounds and instruction arities.  These checks ensure that a value retrieved from the final store still agrees with the value bound earlier in the run.  Each aligned hash must agree across the two primitive implementations on its actual operands.  Each preparation requires a compatible key, instance, proof and guard.  An active preparation parses the key during preprocessing.  An inactive preparation still needs a key that the circuit can parse.  [Producer correspondence](../src/zkir-v4/ProducerCorrespondence.agda) · [Primitive domains](../src/zkir-v4/ProducerSupport.agda) · [RC1 comparison widths](../src/zkir-v4/ComparisonWidths.agda)

**P5, from a witness to a run**.  Given a satisfying witness, the reverse theorem constructs a preimage whose successful run reproduces the value and proof stores, returns, exposed accumulators and statement of the circuit execution.  The reconstructed preimage consumes all its proof slots.  In the equality of circuit states, the remaining slot list is taken from the original circuit witness after its last read.  Circuit satisfaction supplies the initialization, successful instruction steps and final instance check.  Starting with a witness for the chip constraints alone, first normalize its diagnostic entries as in §3.2.  The local replay conditions below apply to that witness.  Producer acceptance supplies the admissible source widths, valid read types and stable declared inputs.  Both extraction theorems assume the canonical codec laws and the backward fixed-key preparation contract.  The latter says that a successful circuit preparation with a parsed key produces the corresponding active VM result, or the trivial accumulator when disabled.  In addition, exact replay needs the following conditions at the instructions executed by the witness.

* The native field value accepted by a successful `Assert` is one.  The circuit tests for a nonzero value.
* The operands of a successful `LessThan` fit the requested width.  The circuit checks the padded width.  When the two widths agree, circuit satisfaction proves the required bounds.
* Each transcript-read guard resolves to a Boolean.  For an inactive read, the witness cell holds the VM default of its declared type.  Each inner-proof guard likewise resolves to a Boolean, and an inactive circuit slot contains the empty blob used by the VM.
* The aligned hash primitives agree on the resolved operand fields.

`producer-extract` takes these local conditions for the particular satisfying witness.  For a producer source in `ReplayFragment.Fragment`, `fragment-extract` derives them for every satisfying witness from the source conditions.  The fragment admits unguarded or literal-one transcript reads, literal-one proof slots and assertions, and comparisons whose padded width equals the requested width.  For each aligned hash, the two primitives must agree for every operand vector at the declared alignment.  The remaining instructions, including guarded impacts, fixed-key preparation, folding and exposure, need no extra fragment restriction.  The variable proof guards in §§7.2–7.3 fall outside this fragment.  For those sources, `one-replay` and `fold-replay` derive the guard from the preparation and preserve both public blocks while rebuilding the consumed proof slots.  This gives statement replay for every satisfying witness.  Exact equality of the private proof stores would additionally require empty inactive slots.  [Residual conditions](../src/zkir-v4/ProducerResiduals.agda) · [Source fragment](../src/zkir-v4/ReplayFragment.agda) · [Disabled-read and proof-slot examples](../src/zkir-v4/ReverseBoundaryExamples.agda)

**Extraction from an honest witness**.  If a producer run on `P` succeeds with final state `Σ`, then `extract(S, honest-witness(P, Σ)) = just(canonical(S, P, Σ))` under the forward preparation contract and the forward primitive conditions on that run.  The canonical preimage replaces inactive proof slots with empty blobs and drops the commitment pair when the commitment is disabled.  It preprocesses to the same final state.  The theorem `producer-honest-round-trip` covers every producer source, including sources with variable guards.  Successful initialization supplies the declared values and their original encoding.  Single assignment preserves those values in the honest witness.  For a witness supplied independently, `producer-extract` still requires the local replay conditions above, which `fragment-extract` supplies for fragment sources.  [Producer correspondence](../src/zkir-v4/ProducerCorrespondence.agda) · [Canonicalization](../src/zkir-v4/StatementUniqueness.agda)

**Extraction and uniqueness**.  Reconstruct declared inputs by encoding their assigned values, active transcript reads by encoding the assigned values in instruction order, and active impact operands from the public input selections.  Reconstruct proof slots in instruction order from active blobs and empty inactive entries.  Recover the commitment pair when enabled and use the same binding input.  If two accepted preimages give the same honest witness and each satisfies the input-agreement and per-step hypotheses of `HonestExplanation`, their canonical representatives agree under the codec and preparation laws.  Equality of the entire honest witnesses is a premise here.  Applying `producer-extract` to an arbitrary satisfying witness yields agreement with the reconstructed circuit state, which retains that witness’s unused proof-slot suffix.  Using uniqueness for that witness requires a separate proof that the candidate runs give the same entire honest witness.  Key location is external to the relation.  [Uniqueness theorem](../src/zkir-v4/StatementUniqueness.agda)

### 8.3 Protocol guarantees

Fix the verifying key generated for `S` and its verifier parameters.  Write `s` for the external statement.  Ledger acceptance includes the count check, outer verification and every deferred pairing.

| Property | Guarantee and hypotheses |
| --- | --- |
| P6. Proving completeness | Given the forward premises of P5, backend completeness for this circuit, and a valid pairing for every accumulator exposed by the run, there exists a proof the ledger accepts for `stmt(Σ)`.  Agda proves this as `complete-from-producer` for the model circuit.  For RC1, `complete-with-comparison-cap` requires every requested `LessThan` width to be at most 252 bits.  For each witness accepted by `check-with-comparison-cap`, the backend must produce proof bytes that verify against that witness’s full public instance.  [RC1 completeness](../src/zkir-v4/ComparisonWidths.agda) |
| P7. Statement soundness | For a producer source in the replay fragment, an accepted proof for `s` yields one preimage whose successful run publishes `s` and exposes exactly the accumulators carried by the proof, in order.  Each of those accumulators passes the ledger pairing check.  This assumes the codec laws, backward preparation and backend extraction for the **full** instance.  Extraction for the chip constraints suffices by the diagnostic equivalence in §3.2.  `sound-on-fragment` proves the implication.  `sound-with-residuals` gives it outside the fragment when the local premises hold for every satisfying witness of the source. |
| Guarded instances of P7 | For the exact sources in §§7.2–7.3, `one-sound` and `fold-sound` reconstruct a successful VM run whose statement equals the caller’s and whose exposed accumulator equals the one carried by the proof.  They use full-instance witness extraction under the source’s outer key, the codec laws and backward preparation.  Circuit satisfaction supplies the guard and its branch-specific replay facts.  In §7.3 the run reproduces the checked fold.  Inferring that each active input to that fold passes its own pairing is the separate security claim in §5.2.  [Guarded statement soundness](../src/zkir-v4/GuardedStatementSoundness.agda) |
| P8. Knowledge soundness | Given the backend's extracted satisfying witness, the circuit extractor computes an explaining preimage under P7's conditions.  Efficient extraction against a probabilistic prover is a cryptographic assumption on the backend.  Agda supplies the witness-to-preimage function and proves its correctness under those conditions. |
| P9. Zero-knowledge | Under the outer proof system's zero-knowledge guarantee, the proof hides witness data beyond the public instance.  The statement and all carried accumulator fields are disclosed.  The cryptographic hiding guarantee is external to the model. |
| P10. Communications binding | When enabled, both passes use the same transient hash on the randomness followed by the ordered, encoded inputs and returns.  Agda defines the commitment from that hash.  Single assignment and canonical encoding identify the two messages.  Binding that public commitment to one message relies on the cryptographic binding of the Poseidon construction.  Its position is second in the external statement, after the accumulator prefix in the full instance. |

[Protocol theorems](../src/zkir-v4/ProducerCorrespondence.agda) · [Verifier acceptance](../src/zkir-v4/Protocol.agda) · [Commitment inputs](../src/zkir-v4/CommitmentInputs.agda)

**Trust boundary**.  The Agda relation specifies what each chip must establish on its assigned cells.  Applying it to Rust assumes that the emitted gates implement those contracts.  Interpreting a recursively verified statement also trusts the fixed-key preparation under its specified transcript, the KZG pairing checks and the key selected by the caller.  For sources that fold, a production soundness bound also needs the computational assumption in §5.2 for the arities the source uses.  The source table identifies each key by the SHA-256 digest of its serialized bytes.  Authenticating the source and deciding which keys to trust belong to the caller.  An application invariant about off-chain witness computation needs its own constraints or protocol check.  The digest read in §7.4 illustrates this boundary.  [Primitive assumptions](../src/zkir-v4/Assumptions.agda) · [Worked example](#74-a-hash-preimage-and-its-public-nullifier)

### 8.4 Mechanization status

The Agda interpreter and circuit model cover all 51 instructions in §4.  The proofs quantify over the [primitive contracts](../src/zkir-v4/Assumptions.agda).  Correspondence between these contracts and the Rust libraries is a separate implementation assumption.  The [v4 module guide](../src/zkir-v4/README.md) gives the build entry point and proof dependencies.  `PackingRoundTrip.round-trip` instantiates both directions on the successful byte-packing run in §7.1.  For every binding input it gives the honest satisfying witness, an extracted preimage, and successful replay with the honest circuit state, whose remaining slot list is empty.  [Worked proof](../src/zkir-v4/CorrespondenceExamples.agda)

| Property | Proved in the v4 model |
| --- | --- |
| Source checks | `validate` checks proof binding and single use, accumulator consumption and fixed-key table coverage.  `producer?` also checks single assignment, types, widths, arities and output placement.  `compute-types` proves that every successful pure computation writes exactly the inferred names and types.  [Validator](../src/zkir-v4/Validation.agda) · [Producer](../src/zkir-v4/Producer.agda) · [Write typing](../src/zkir-v4/ProducerCompute.agda) |
| Recursive verification | [Accounting for active preparations](#52-preparation-folding-and-exposure) · [Separate and folded verification](#53-checking-two-proofs-separately-or-together) · [Sequential counter](#54-proving-a-sequence-of-exactly-n-transitions) · [Proof trees](#55-proving-a-tree-of-application-claims) · [Splitting, joining and regrouping](#56-splitting-and-joining-counter-segments) |
| Typed encoding | `encode-width` proves the field width for every type.  `decode-typed` and `decode-encode-sound` prove the claimed type and canonical encoding of every decoded result.  `encode-decode` proves the inverse direction on admissible values using the assumed inherited field and curve codecs, one native chunk inversion law, and one G1 field codec law.  [Encoding properties](../src/zkir-v4/EncodingProperties.agda) |
| Declared input stream | `decode-inputs-sound` recovers the ordered list of canonical typed values from a successful stream decode and shows that their encoding reproduces the complete input.  `decode-inputs-round` proves reconstruction under the codec assumptions.  [Input properties](../src/zkir-v4/InputProperties.agda) |
| Circuit initialization | `init-forward` and `init-backward` relate the two initial stores and statement seeds under the codec laws, ordered input agreement for the forward direction, and valid declared types for the reverse direction.  The circuit takes the supplied witness slots while preprocessing keeps its own proof stream.  [Circuit input properties](../src/zkir-v4/CircuitInputs.agda) |
| Preimage uniqueness | `canonical-accepted` preserves the accepted run after erasing inactive proof bytes and a disabled commitment.  `extract-explanation` recovers the canonical preimage from a satisfying honest witness generated by an accepted run, under the codec and preparation laws, ordered input agreement and local correspondence along the run.  For successful producer runs, `producer-honest-round-trip` recovers the canonical preimage under the forward preparation contract and the run’s forward primitive conditions.  `explanations-unique-modulo-erasure` equates the canonical representatives of two such explanations for the same witness.  [Statement uniqueness](../src/zkir-v4/StatementUniqueness.agda) |
| Extracted witness | `extracted-witness-complete` proves that the rebuilt witness for an extracted preimage satisfies the circuit.  It assumes a satisfying original witness with a replay trace, valid declared types and stable committed inputs when enabled.  The rebuilt witness must meet the ordered input and local instruction conditions of `RebuiltShape`.  The theorem equates the returned statement, carried accumulators and full public input to those of the original circuit.  [Extracted witness](../src/zkir-v4/ExtractedWitness.agda) |

## Appendix A. Glossary

| Term | Meaning in this specification |
| --- | --- |
| Source producer | The compiler or other author of an IR source.  `Producer` is the Agda predicate on sources used in §8.2. |
| Preimage | Call data supplied to preprocessing, including declared inputs, transcripts, binding input, optional commitment opening and inner-proof slots. |
| Witness | An assignment used to satisfy the circuit.  The honest witness is the assignment obtained from a successful VM run. |
| Transcript | In a preimage, an ordered stream of values exchanged with the VM.  In a proof protocol, the hash transcript used to derive cryptographic challenges.  Section 6 specifies which transcript the outer and inner proofs use. |
| Impact | An instruction reserving a group of statement fields.  Its guard selects the resolved native operands or an equal number of zeros. |
| Binding input | The first field of the external statement, supplied with the call.  Its application meaning comes from the calling protocol. |
| External statement and full instance | The caller supplies the external statement.  The verifier builds the full vector of circuit public inputs by prefixing the encoded carried accumulators. |
| Accumulator | A pair of group elements representing a deferred opening equation.  An exposure places its encoding in the circuit instance and its deferred check in ledger verification. |
| Replay | Reconstruction of a preimage from a satisfying witness, followed by VM execution to recover the modeled circuit state. |

## Appendix B. Reading v4 from the v3 specification

These are the interfaces at the two specification pins.  The type-support table in §4.3 gives the v4 domains for individual operations.  Of the 51 v4 instructions, variants 0–33 form the v3.0 set, variants 34–46 belong to v3.1, and variants 47–50 implement recursive verification in v4.  [Rust instruction variants](../../zkir/src/ir.rs#L1314) · [V3 reference at its pin](zkir-v3-spec.md) · [V4 pin and coverage](zkir-v4-plan.md)

| Interface | IR 3.0 | IR 4.0 |
| --- | --- | --- |
| Types and instructions | 13 types and 34 instructions.  Byte strings have length 32. | 16 type constructors and 51 instructions.  `Bool`, `Byte` and `Accumulator` are distinct types, and `Bytes(n)` carries its length.  A guard still uses a native bit. |
| Byte conversion and hashing | `Bytes32IntoLowHigh` and `Bytes32FromLowHigh` split and reconstruct a 32-byte string. | `BytesIntoNatives` and `BytesFromNatives` handle a length-dependent number of fields.  `ToBytes` and `FromBytes` also cover compressed points.  The byte-hash family includes SHA-512. |
| `Impact(g, [])` | The v3 circuit model emits no guard constraint for an empty input list. | The circuit checks that `g` is a native bit even when the list is empty. |
| `ReconstituteField` | The circuit checks the parts and their field equation.  The witness-shape condition supplies the integer no-overflow bound. | The circuit splits the canonical result into bits and checks both parts.  This enforces the no-overflow bound on every satisfying assignment. |
| Recursion and call data | The preimage has three field streams.  The source has no inner-key table. | A fourth stream carries inner proofs.  The source fixes the inner keys, prepares proofs, folds accumulators and exposes them for deferred checking. |
| What the verifier receives | The circuit public inputs are the binding input, optional commitment and impacts. | These fields remain the external statement.  Each accumulator carried by the proof contributes a 12-field prefix block to the full circuit instance, in exposure order. |
| Uniqueness for a fixed witness | For a well-typed producer, every satisfying witness meeting `WShape` has a realizer.  All its realizers agree on the preimage and final state when the commitment pair is present exactly when enabled. | Two accepted runs satisfying `HonestExplanation` and giving the same entire honest witness have equal canonical preimages under the codec and preparation laws.  Canonicalization also erases inactive proof bytes.  Section 8.2 gives the separate replay guarantee for an arbitrary satisfying witness. |
