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

These checks establish inventory drift only. The next integration step is to compare Clean's
built-in Rust AIR/witness output here. The Lean semantic profile and existing migration evidence
remain on their separately recorded revision until that comparison and the semantic review pass.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track the migration in [#112](https://github.com/dtumad/sp1-lean/issues/112).
