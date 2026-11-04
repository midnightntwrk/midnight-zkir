# Changelog

## Unreleased

## ZKIR 3.2.0

First final (non-pre-release) ZKIR 3.x release. It covers everything since
the repository was split out of midnight-ledger at `zkir-3.0.0-rc.1`,
including the changes previously shipped only in `3.1.0-rc.1`, `3.2.0-rc.1`
and `3.2.0-rc.2`.

### IR language

- feat: accept IR version 3.2 (`IrMinorVersion::V2`, now the default); 3.0
  and 3.1 IR still loads. The minor version is a label only: no instruction
  is gated on it.
- feat: new types `Bool`, `Byte`, and `Bytes(n)` (`1 <= n <= 2^24`), which
  generalizes `Bytes32`.
- feat: new instructions `Slice`, `Nth`, `Concat`, `Reverse`,
  `LoadConstant`, `Sha512`, `And`, `Or`, `Xor`, `ToBytes`, `FromBytes`,
  `BytesIntoNatives` and `BytesFromNatives`.
- feat: `ToBytes`/`FromBytes` support all prime-field types, including
  `JubjubScalar`. `FromBytes` accepts any length and reduces modulo the field
  order, for example to reduce a SHA-512 digest into a `Curve25519Scalar`.
- feat: `ToBytes`/`FromBytes` support curve points in compressed form:
  ed25519-style 32 bytes for `JubjubPoint` and `Curve25519Point`, and SEC1
  33 bytes for `Secp256k1Point` and `Secp256r1Point`, with the identity
  encoded as 33 zero bytes. Non-canonical point encodings are rejected.
- feat: `Add`, `Mul`, `Neg`, `Inv`, `TestEq`, `ConstrainEq` and `CondSelect`
  support `JubjubScalar`.
- feat: `EcMulGenerator` supports `Secp256r1Scalar` and `Curve25519Scalar`.
- deprecated: `IntoBytes32`, `FromBytes32`, `ReverseBytes`,
  `Bytes32IntoLowHigh`, `Bytes32FromLowHigh`, `DivModPowerOfTwo` and
  `ReconstituteField`. They are kept for ZKIR 3.0 compatibility. Use
  `ToBytes`, `FromBytes`, `Reverse`, `BytesIntoNatives` and
  `BytesFromNatives` instead.

### Fixes

- fix: `ReconstituteField` constrains its result to the canonical
  representation. The previous range checks allowed
  `divisor * 2^bits + modulus` to exceed the field modulus and wrap around.
- fix: decoding circuit inputs rejects non-canonical encodings. Previously,
  for example, a Jubjub point whose `x` coordinate had been tampered with
  could decode to the same point.
- fix: keep the ZKIR 3.0 binary layout of `Instruction` and `IrType` and the
  ZKIR 3.0 circuit for `Encode` on `Bytes(32)`, so existing 3.0 IR keeps its
  serialization.

### Performance

- perf: avoid eager error construction and redundant clones (enforced by
  the clippy `or_fun_call` and `redundant_clone` lints).

### Dependencies

- Bump `midnight-circuits` to 7.3.0 and `midnight-zk-stdlib` to 2.4.0, and
  move off their deprecated coordinate accessors. SEC1 `ToBytes`/`FromBytes`
  keep encoding the identity as 33 zero bytes with the new accessors.
- Update `rustls` to 0.23.45 (cargo audit) and apply further `cargo audit`
  fixes.

### Packaging and release

- breaking: the `zkir-v3` crates are consolidated into `midnight-zkir` 3.x
  and `midnight-zkir-wasm` 3.x. The major version now separates v2 from v3,
  and the v2 crates are no longer built from this repository.
- The WASM bindings are published to npm as `@midnightntwrk/zkir-v3` and
  `@midnight-ntwrk/zkir-v3`. The JavaScript API is unchanged from
  3.0.0-rc.1.
- Add Prepare/Publish release workflows: npm dist-tags for pre-releases and
  crates.io publishing for final releases.
- Add the ZKIR v3 language specification and Agda mechanization under
  `zkir-spec`.
