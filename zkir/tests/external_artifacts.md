# verify_proof end-to-end — QA runbook

Two examples: **cred_ledger** (`DeciderKind::None`) and **ivc_ledger**
(`DeciderKind::Collapsed`). Artifacts are already checked into
`zkir-v3/tests/assets/`, so the ledger-side test runs standalone. You only touch
midnight-zk to regenerate them.

## Prerequisites

- `cargo +1.95.0` in both repos.
- Midnight SRS at `$MIDNIGHT_PP` or default `~/.cache/midnight/zk-params`.
  Required: `bls_midnight_2p5` through `bls_midnight_2p21`. A Filecoin SRS will
  not pair — do not substitute.
- Two working trees:
  - midnight-ledger, branch `iquerejeta/decidable_v2`
  - midnight-zk, branch `iquerejeta/examples-verify-proof-v2` (the
    `zk-stdlib-v2` lineage — do **not** use `main`, `MidnightVK::read`
    desynchronises against a `main`-built VK).

## Fast path — verify what's already checked in

1. Structural / off-circuit check (<1 s, no SRS needed):
   ```
   cargo +1.95.0 test -p midnight-zkir-v3 --release \
       --test external_artifacts -- --nocapture
   ```
   Expected on success:
   ```
   [cred_ledger] ok - None, k=17, 5 instance fields, 12 accumulator fields exposed
   [ivc_ledger]  ok - Collapsed, k=19, 14 instance fields, 12 accumulator fields exposed
   test external_artifacts_are_readable ... ok
   test result: ok. 1 passed; 0 failed; 1 ignored
   ```

2. Full end-to-end (~14 min — do **not** kill this):
   ```
   cargo +1.95.0 test -p midnight-zkir-v3 --release \
       --test external_artifacts -- --ignored --nocapture
   ```
   Expected:
   ```
   [cred_ledger] end-to-end ok (None)
   [ivc_ledger]  end-to-end ok (Collapsed)
   test result: ok. 1 passed; 0 failed; ... finished in ~814s
   ```

A pass proves, per artifact: (a) statement soundness of the outer PLONK proof
containing the ZKIR `verify_proof` instruction, and (b) discharge of the
deferred KZG accumulator via the pairing check in `VerifierKey::verify`
(`transient-crypto/src/proofs.rs`). For `Collapsed`, the inner IVC accumulator
was already folded into the outer accumulator in-circuit; one pairing at the
outer level discharges both.

## Regeneration path — rebuild the artifacts

Only needed when the inner circuits or serialization format change. From a
midnight-zk checkout on the `zk-stdlib-v2` lineage:

### cred_ledger (`DeciderKind::None`, k=17, ~25 s)

```
cargo +1.95.0 run --release -p midnight-zk-stdlib --example cred_ledger
```

Emits into `<midnight-zk>/zk_stdlib/examples/assets/ledger/cred_ledger/`:
`vk.bin`, `vk_ledger.bin` (tagged blob = 1-byte `DeciderKind` ++ `MidnightVK`),
`proof.bin`, `instance.hex`. Prints `LEDGER vk_hash = …` and self-checks the
ledger's off-circuit path before writing.

Copy the three consumed files to the ledger:
```
cp <midnight-zk>/zk_stdlib/examples/assets/ledger/cred_ledger/{vk_ledger.bin,proof.bin,instance.hex} \
   <midnight-ledger>/zkir-v3/tests/assets/cred_ledger/
```

### ivc_ledger (`DeciderKind::Collapsed`, k=19, ~5 min)

```
cargo +1.95.0 run --release -p midnight-aggregation --example ivc_ledger
```

Real IVC chain — `PoseidonChain`, `N = 8` Poseidon rounds per step, `STEPS = 3`,
`IVC_K = 19`. `N` was 1000; `k` is dominated by the in-circuit verifier not
Poseidon, so shrinking `N` cuts proving time but does not drop `k`. Finalises
the chain into a single PLONK proof whose circuit `collapse →
resolve_fixed_bases → collapse`s the accumulator before exposing it. Emits into
`<midnight-zk>/aggregation/examples/assets/ledger/ivc_ledger/` with the same
file set.

Copy:
```
cp <midnight-zk>/aggregation/examples/assets/ledger/ivc_ledger/{vk_ledger.bin,proof.bin,instance.hex} \
   <midnight-ledger>/zkir-v3/tests/assets/ivc_ledger/
```

Then rerun both steps of the fast path.

## What the ZKIR side does with those files

`zkir-v3/tests/external_artifacts.rs` builds the outer IR inline: it hashes
`vk_ledger.bin` to `vk_hash`, feeds the inner instance in as `private_input`
fields plus `proof.bin` as an `InnerProofWitness::Direct` inside a
`ProofPreimage`, runs `verify_proof`, and (for `Collapsed`) applies
`decide_incircuit`. `$MIDNIGHT_ZK_ARTIFACTS` overrides the default
`zkir-v3/tests/assets/` lookup.

The pre-existing `zkir-v3/tests/verify_proof_e2e.rs` (toy `Echo` / `Recursive`
relations) is untouched — the two real examples live in a separate test file so
the toy tests remain the fast smoke suite.

## Removed

- `zkir-v3/tests/gen_recursive_asset.rs.wip` — superseded by the two real
  generators in midnight-zk.
