# Checking the ZKIR specifications

The repository contains separate Markdown and Agda specifications for each version.

| Language | Reference | Mechanization |
| --- | --- | --- |
| IR 4.0 | [ZKIR v4](../docs/zkir-v4-spec.md) | [Modules and theorem hypotheses](zkir-v4/README.md) |
| IR 3 | [ZKIR v3](../docs/zkir-v3-spec.md) | [Modules and theorem hypotheses](zkir-v3/README.md) |

Run both aggregate checks with the pinned Agda toolchain used by CI.

```sh
cd zkir-spec/src
nix run .#agda -- --safe zkir-v3/Main.agda
nix run .#agda -- --safe zkir-v4/Main.agda
```

Each entry point imports its version's entire development.  A cold build takes several minutes.  The flake supplies Agda and the libraries listed in the [Agda project file](zkir-formal-spec.agda-lib).  The [CI workflow](../../.github/workflows/agda.yml) checks both versions when a specification changes.
