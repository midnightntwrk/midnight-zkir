# Changelog

## Unreleased

- feat: `sow-26q3` cargo feature (default on) gating 2026-Q3 functionality:
  the Secp256r1 and Curve25519 types, and all ZKIR 3.1 types and instructions.
  Without it, `IrSource::load`, tagged loading, `check`/`prove` and keygen
  refuse such IR with a `FeatureGateError`. Ledger 9 builds with
  `default-features = false`.
