# Changelog

## Unreleased

- Add the `prepare_verification` and `inner_proof` instructions, with the circuit's
  verifying keys carried in `IrSource::inner_vks`. Breaking: a `V1`
  binary `IrSource` now carries `inner_vks`, so 3.1 binary files
  written before this change no longer deserialize.
- Add the `Accumulator` type and the `accumulate` and
  `verify_accumulator` instructions (ZKIR 4). `prepare_verification`  outputs an
  accumulator, which must reach exactly one `verify_accumulator` (possibly
  through `accumulate`).
