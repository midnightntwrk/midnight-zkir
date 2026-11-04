# ZKIR 3.2.0 Release Notes

**Version:** 3.2.0
**Date:** 2026-11-04

## High-level summary

ZKIR 3.2.0 is the first final release of ZKIR 3.x. Earlier 3.x versions
(3.0.0-rc.1, 3.1.0-rc.1, 3.2.0-rc.1 and 3.2.0-rc.2) were pre-releases only.
These notes cover everything since ZKIR was split out of midnight-ledger at
3.0.0-rc.1.

The release greatly expands the IR language. It adds `Bool`, `Byte`, and
variable-length `Bytes(n)` types; byte-string operations (`Slice`, `Nth`,
`Concat`, `Reverse`); boolean gates; SHA-512; constants; and byte
conversions for every prime-field type and every curve point. It also
contains two soundness fixes: `ReconstituteField` now enforces a canonical
result, and decoding circuit inputs now rejects non-canonical encodings.
Existing ZKIR 3.0 and 3.1 IR still loads and keeps its serialization. IR
version 3.2 is now the default.

## Audience

This release note is important for:

- Compact compiler developers emitting ZKIR 3.x
- Developers using the ZKIR WASM bindings (`@midnightntwrk/zkir-v3`)
- Rust consumers of the `midnight-zkir` crate
- Anyone holding proving/verifying keys generated with a ZKIR 3.x
  pre-release

## Summary of updates

### IR language updates

- IR version 3.2 (`IrMinorVersion::V2`) is accepted and is the default. 3.0
  and 3.1 IR still loads. The minor version is a label only: no instruction
  is gated on it.
- New types: `Bool`, `Byte`, and `Bytes(n)` for `1 <= n <= 2^24`.
  `Bytes(n)` generalizes `Bytes32`.
- New byte-string instructions: `Slice`, `Nth`, `Concat`, and `Reverse`.
- New instructions `BytesIntoNatives` and `BytesFromNatives` pack `Bytes(n)`
  into, and unpack it from, 31-byte native field elements. They are a
  temporary bridge for Compact.
- New boolean gates: `And`, `Or`, and `Xor` over non-empty lists of `Bool`.
- New `LoadConstant` instruction loads a fixed value of any type, given as
  its canonical encoding.
- New `Sha512` instruction outputs `Bytes(64)`. The SHA-512 chip is enabled
  only for circuits that use it.
- New `ToBytes`/`FromBytes` instructions:
  - They support every prime-field type: `Native`, `JubjubScalar`, and the
    base and scalar fields of Secp256k1, Secp256r1 and Curve25519.
    `FromBytes` accepts any length and reduces modulo the field order, for
    example to reduce a SHA-512 digest into a `Curve25519Scalar`.
  - They support curve points in compressed form: 32 bytes for
    `JubjubPoint` and `Curve25519Point`, and 33-byte SEC1 for
    `Secp256k1Point` and `Secp256r1Point`, with the identity encoded as 33
    zero bytes. Non-canonical point encodings are rejected.
- `Add`, `Mul`, `Neg`, `Inv`, `TestEq`, `ConstrainEq` and `CondSelect` now
  support `JubjubScalar`.
- `EcMulGenerator` now supports `Secp256r1Scalar` and `Curve25519Scalar`.

### Proving backend updates

- `midnight-circuits` is bumped to 7.3.0 and `midnight-zk-stdlib` to 2.4.0.
- Clippy `or_fun_call` and `redundant_clone` lints are now enforced
  workspace-wide. This avoids eager error construction and redundant clones.
- Dependency security updates are applied: `rustls` 0.23.45 and other
  `cargo audit` fixes.

### Packaging and distribution updates

- The `zkir-v3` crates are consolidated into `midnight-zkir` and
  `midnight-zkir-wasm`, versioned 3.x. The major version now distinguishes
  ZKIR v2 from v3.
- The WASM bindings are published to npm as `@midnightntwrk/zkir-v3` and
  `@midnight-ntwrk/zkir-v3`. The JavaScript/TypeScript API (`zkir.d.ts`) is
  unchanged from 3.0.0-rc.1.
- Releases are cut with the new Prepare and Publish ZKIR Release workflows
  (see `RELEASES.md`). Pre-releases are published under a matching npm
  dist-tag.
- The ZKIR v3 language specification and its Agda mechanization are
  available under `zkir-spec`.

## New features requiring configuration updates

*None in this release.*

## Deprecations

The following instructions are kept only so that ZKIR 3.0 circuits continue
to load and prove. They are slated for removal and should not be used in new
circuits:

| **Deprecated instruction** | **Replacement**       |
|----------------------------|-----------------------|
| `IntoBytes32`              | `ToBytes`             |
| `FromBytes32`              | `FromBytes`           |
| `ReverseBytes`             | `Reverse`             |
| `Bytes32IntoLowHigh`       | `BytesIntoNatives`    |
| `Bytes32FromLowHigh`       | `BytesFromNatives`    |
| `DivModPowerOfTwo`         | *(none)*              |
| `ReconstituteField`        | *(none)*              |

## Breaking changes or required actions for developers

- **Regenerate keys built with a ZKIR 3.x pre-release.** The
  `ReconstituteField` soundness fix changes the constraints of every circuit
  that uses it, at any IR minor version. Keys from 3.0.0-rc.1 or
  3.1.0-rc.1 no longer match those circuits, and the `midnight-zk` upgrade
  can also change circuit layout. Regenerate proving and verifying keys
  with 3.2.0.
- **Rust: `midnight-zkir` 3.x is ZKIR v3 only.** The latest crate on
  crates.io before this release was `midnight-zkir` 2.1.1, which implements
  ZKIR v2. Consumers that still need v2 should pin `^2`.
- **IR that declares version 3.2 needs ZKIR 3.2.** Older 3.0 and 3.1 builds
  reject JSON IR with `"minor": 2` and binary IR serialized with
  `IrMinorVersion::V2`.

## Fixed defect list

| **Component** | **Description** |
|---------------|-----------------|
| zkir (circuit) | `ReconstituteField` now constrains its result to the canonical representation. Previously, `divisor * 2^bits + modulus` could exceed the field modulus and wrap around. |
| zkir (decoding) | Decoding circuit inputs now rejects non-canonical encodings. Previously, for example, a Jubjub point with a tampered `x` coordinate could decode to the same point. |
| zkir (serialization) | The ZKIR 3.0 binary layout of `Instruction`/`IrType` and the 3.0 `Encode` circuit for `Bytes(32)` are preserved. |
| zkir (proptest) | Property tests cover the Secp256r1 and Curve25519 IR types again. |
| zkir-wasm (packaging) | npm packaging is fixed after the crate consolidation. It previously still referenced the removed `zkir-v3.d.ts` and the `zkir-v2` package name. |
