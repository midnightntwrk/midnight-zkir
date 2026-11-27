# Maintaining the IR 4.0 specification

The implementation target is the release tag `zkir-4.0.0-rc.1` at `3ec876c0a311e4979536ae432d2c810e324ace64`.  The reference covers the 51 instruction variants and 16 type constructors at this pin.  Agda is the in-repository mechanization.  The build retains a separate entry point for IR 3.  [Target source](https://github.com/midnightntwrk/midnight-zkir/tree/3ec876c0a311e4979536ae432d2c810e324ace64) · [IR 4.0 reference](zkir-v4-spec.md) · [Agda modules and theorem hypotheses](../src/zkir-v4/README.md)

## Which sources apply

| Source | Scope |
| --- | --- |
| [Versioned v3 reference](zkir-v3-spec.md) and [Agda](../src/zkir-v3/README.md) | The v3 specification pin has 34 instructions and 13 types.  Thirteen inherited operations and the generalized byte and Boolean types are part of the v4 reference, alongside four recursive instructions and the accumulator type. |
| [Draft PR #101](https://github.com/midnightntwrk/midnight-zkir/pull/101) and [draft reference](https://github.com/midnightntwrk/midnight-zkir/blob/58f9176069505623317c60725f129b644edf16c5/zkir-spec/docs/zkir-v4-spec.md) | The draft specifies a different key design, including private-key slots, binding and a Poseidon-based key identifier.  Even fixed keys use a different reference.  The release addresses processed fixed keys by SHA-256 of their source bytes. |
| [MinoCrab Lean syntax](https://github.com/sig-net/minocrab/blob/258ec945b6c38e94d6152971dab3da1ba8435adf/crates/minocrab-zkir/lean/MinocrabZkir/Syntax.lean) and [completeness result](https://github.com/sig-net/minocrab/blob/258ec945b6c38e94d6152971dab3da1ba8435adf/crates/minocrab-zkir/lean/MinocrabZkir/Completeness.lean) | This independent v3 model covers a compiler-emitted subset.  Its Lean proof concerns that subset, including specialized 32-byte operations.  The upstream refs inspected for this work contain the Agda development. |

## How to update the pin

1. Compare the target commit, [lockfile](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/Cargo.lock), [Rust syntax](../../zkir/src/ir.rs), [types](../../zkir/src/ir_types.rs), serialization tags and loader.  Check the [v3 merge workflow](../../.github/workflows/merge-to-next.yml) for inherited language changes.  Preserve the variant order and the external JSON names in the reference.
2. Compare both dispatches in the [VM](../../zkir/src/ir_vm.rs), the [instruction helpers](../../zkir/src/ir_instructions) and the [types pass](https://github.com/midnightntwrk/midnight-zkir/blob/3ec876c0a311e4979536ae432d2c810e324ace64/zkir/src/type_inference.rs).  Update preprocessing, constraints, producer conditions and boundary examples together.  Compare the types of intermediate cells as well as declared inputs.
3. Trace changes to recursive verification through source validation, witness slots, the fixed-key table, folding, both public-input blocks and the pinned ledger verifier.  If the key design changes, replace the grammar, examples, witness layout and proof premises from the tagged implementation.
4. Check the hypotheses and conclusions of the forward, extraction, uniqueness and protocol theorems.  Distinguish the returned statement from the reconstructed full circuit instance.  Record any new primitive contract or witness-shape condition alongside its declaration.
5. Run both Agda entry points on the spec branch and the Rust suite against the release lockfile.  The documentation tests load the JSON fences in the reference, substitute a real processed key for the indicated fixture, and check both guards.  The separate recursive suite exercises proving and verification with real parameters.

```sh
(cd zkir-spec/src && nix run .#agda -- --safe zkir-v3/Main.agda)
(cd zkir-spec/src && nix run .#agda -- --safe zkir-v4/Main.agda)
```

To check the Rust examples against RC1, start in the spec repository root.  The test modules live on this branch.  Copy them and the reference into a checkout of the release so Cargo builds the tagged implementation and its dependencies.

```sh
rc_dir=$(mktemp -d)
git clone --branch zkir-4.0.0-rc.1 --depth 1 https://github.com/midnightntwrk/midnight-zkir.git "$rc_dir"
cp zkir/src/spec_examples.rs zkir/src/sequential_counter.rs "$rc_dir/zkir/src/"
mkdir -p "$rc_dir/zkir-spec/docs"
cp zkir-spec/docs/zkir-v4-spec.md "$rc_dir/zkir-spec/docs/"
cat >> "$rc_dir/zkir/src/lib.rs" <<'RUST'
#[cfg(test)]
mod sequential_counter;
#[cfg(test)]
mod spec_examples;
RUST
cd "$rc_dir"
nix develop -c cargo test -p midnight-zkir --locked --release
nix develop -c cargo test -p midnight-zkir --locked --release --lib verify_reference_proofs -- --ignored
nix develop -c cargo test -p midnight-zkir --locked --release --lib sequential_counter::depth_two_counter_matches_sequential_source -- --ignored --exact
nix develop -c cargo test -p midnight-zkir --locked --release --test verify_proof_e2e -- --ignored --test-threads=1
```
