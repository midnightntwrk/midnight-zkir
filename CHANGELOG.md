# Changelog

## Unreleased

- Add the `prepare_verification` and `inner_proof` instructions, with the circuit's
  verifying keys carried in `IrSource::inner_vks`, which a binary
  `IrSource` encodes from the new default `IrMinorVersion::V3` on.
- Add the `Accumulator` type and the `accumulate` and
  `verify_accumulator` instructions (ZKIR 4). `prepare_verification`  outputs an
  accumulator, which must reach exactly one `verify_accumulator` (possibly
  through `accumulate`).
