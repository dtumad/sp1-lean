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

These checks establish inventory drift only. The optional `clean-export` feature tests freshly
generated Clean Rust with the backend pinned to the same revision as the Lean emitter:

```sh
bash scripts/check_ensemble_export.sh
```

The runner builds the Lean fixture and writes Rust plus Lean reference rows to a fresh ignored
directory. Cargo compiles that exact output, compares generated cells, proves both allowed values,
and rejects forged membership, altered public values, row contents and table shapes. The fixture
uses verifier-fixed columns and Clean's witness scheduler; it does not yet compare instruction AIR
against SP1. Test FRI parameters exercise the API and are not deployment security parameters.

The default `inventory` feature retains the existing SP1 checks. The export runner uses
`--no-default-features --features clean-export` so the backend fixture need not compile SP1's
executor. Future instruction comparisons can enable both features in this crate.

The Lean semantic profile and existing migration evidence remain on their separately recorded
revision until instruction comparisons and the semantic review pass.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track the migration in [#112](https://github.com/dtumad/sp1-lean/issues/112).
