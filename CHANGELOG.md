# Changelog

## Unreleased

- Add the `verify_proof` and `inner_proof` instructions, with the circuit's
  verifying keys carried in `IrSource::verify_proof_vks`. Breaking: a `V1`
  binary `IrSource` now carries `verify_proof_vks`, so 3.1 binary files
  written before this change no longer deserialize.
- Add the `Accumulator` type and the `accumulate` and
  `verify_accumulator` instructions (ZKIR 4). `verify_proof` now outputs an
  accumulator, which must reach exactly one `verify_accumulator` (possibly
  through `accumulate`). This replaces `DeciderKind`: an
  accumulator an inner proof carries is witnessed like any other value, and
  `verify_proof_vks` entries are plain `MidnightVK` blobs, with no tag byte.
