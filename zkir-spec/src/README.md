# Agda development — toolchain and type-checking

This directory holds the Agda mechanization of ZKIR v3
([zkir-v3/](zkir-v3/), spec at
[../docs/zkir-v3-spec.md](../docs/zkir-v3-spec.md)) and the Nix flake
providing the toolchain (the same one CI uses, via
[.github/workflows/agda.yml](../../.github/workflows/agda.yml)).

Everything runs from this directory via the flake:

```sh
cd zkir-spec/src
nix run .#agda -- zkir-v3/Main.agda    # type-checks the entire development
```

Inside a nix shell (or with a suitable Agda + standard-library setup) the
bare invocation works from the repository root:

```sh
agda --safe -i zkir-spec/src zkir-spec/src/zkir-v3/Main.agda
```

`Main.agda` imports every module, so checking it verifies the whole
development. `zkir-v3/CircuitFaithfulness.agda` (~4100 lines) is large — a
cold check can take several minutes. Dependencies are declared in
[zkir-formal-spec.agda-lib](zkir-formal-spec.agda-lib) (`standard-library`,
`standard-library-classes`, `standard-library-meta`).
