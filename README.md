# midnight-zkir

The zero-knowledge intermediate representation (ZKIR) used by the [Midnight](https://midnight.network) network.

ZKIR is the circuit format that the [Compact](https://docs.midnight.network/develop/reference/compact/) compiler targets. This repository contains the IR definition, the virtual machine that evaluates it, and the tooling that compiles ZKIR circuits into PLONK proving and verifying keys.

## Repository layout

- `zkir/` — the `midnight-zkir` crate: the IR types, instruction set, and VM, plus the `zkir` CLI binary (behind the `binary` feature) with `compile`, `compile-many`, `mock-compile`, and `mock-compile-many` subcommands for turning `.zkir` files into prover/verifier keys.
- `zkir-wasm/` — WASM bindings (`midnight-zkir-wasm`) exposing the checker and prover to JavaScript via `wasm-bindgen`.
- [ZKIR specifications](zkir-spec/src/README.md) — versioned language references and Agda models, including the [IR 4.0 specification](zkir-spec/docs/zkir-v4-spec.md).

## Building

With [Nix](https://nixos.org/) (recommended — provides the pinned Rust toolchain and public parameters):

```sh
nix develop        # enter a dev shell
nix build          # build the zkir CLI
```

With plain Cargo:

```sh
cargo build --release --features binary
cargo test
```

## Usage

Compile a directory of ZKIR circuits into proving/verifying keys:

```sh
zkir compile-many <ir-dir> <output-dir>
```

Use `zkir --help` for the full set of subcommands and options.

## Contributing

See [CONTRIBUTING.md](CONTRIBUTING.md) for guidelines, and [CODE_OF_CONDUCT.md](CODE_OF_CONDUCT.md) for our code of conduct.

## Security

Please report security issues following the process in [SECURITY.md](SECURITY.md) — use GitHub's private vulnerability reporting, not public issues.

## License

Licensed under the [Apache License, Version 2.0](LICENSE).
