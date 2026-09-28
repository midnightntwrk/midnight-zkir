# Changelog

## Unreleased

- Add the `verify_proof` and `inner_proof` instructions, with the circuit's
  verifying keys carried in `IrSource::verify_proof_vks`. Breaking: a `V1`
  binary `IrSource` now carries `verify_proof_vks`, so 3.1 binary files
  written before this change no longer deserialize.
