# Released SP1 comparison

This crate reads the installed AIR inventory directly from SP1 v6.8.1. Its Git dependency
and Cargo lockfile are independent of the legacy Rust-to-Lean extraction checkout.

```sh
cargo test --locked --manifest-path rust/sp1-comparison/Cargo.toml
cargo test --locked --manifest-path rust/sp1-comparison/Cargo.toml --features mprotect
```

The two reviewed inventories record the field, public-input width, mode-associated columns
and every cluster occurrence. Shared layout records reduce repetition; cluster indices retain
order and repeated entries. A pin or layout change fails the snapshot test and needs review.
Regenerate explicitly with `cargo run --locked --manifest-path rust/sp1-comparison/Cargo.toml`,
adding `--features mprotect` for that configuration.

The inventory checks establish layout drift only. Fresh Clean Rust is compiled against the backend
pinned to the same revision as the Lean emitter and compared with SP1:

```sh
bash scripts/check_ensemble_export.sh
```

The runner checks two byte-identical generations under `.lake/ensemble-export/`. Cargo compiles
that output and exercises two boundaries:

- The fixed-membership ensemble uses verifier-fixed columns and Clean's scheduler. Generated cells
  match Lean; backend proofs accept both allowed values and reject forged membership, changed public
  values, rows and table shapes. Test FRI parameters are not deployment security parameters.
- The production ADD component's generated witnesses match all 81 event and 15 padding rows from
  SP1's live trace generator. Direct field evaluation compares local constraint satisfaction and
  complete interaction multisets, also across 396 column mutations. Repeated messages and zero
  multiplicities are retained. Both Cargo configurations, with and without `mprotect`, run this
  **supervisor-mode** comparison with trusted-program public values.

The instruction fixture has open external buses. A test-only `Program` adapter uses Clean's runtime
to construct the local row without scheduling those buses; the unadapted program is checked to
reject an active row without providers. This is not a full-ensemble acceptance or completeness test.
The layout adapter moves ADD's selector from the last to the first column. Channel adaptation
reverses Byte, Memory and Program signs to match Clean's provider-to-consumer guarantee direction.

The default `inventory` feature retains the independent inventory checks. `clean-export` enables
the backend fixture alone; `instruction-export` also enables the live SP1 instruction comparison.

The Lean semantic profile and existing migration evidence remain on their separately recorded
revision until instruction comparisons and the semantic review pass.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track remaining instruction and provider coverage in [#28](https://github.com/dtumad/sp1-lean/issues/28)
and [#29](https://github.com/dtumad/sp1-lean/issues/29).
