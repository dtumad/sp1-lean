# Rust comparison tools

`witgen-interp/` consumes the current [JSON witness format](../docs/witgen-wire-format.md).
It is a transitional comparison tool. The intended replacement is
[Clean’s direct Lean → Rust export](../docs/export.md), with thin SP1 adapters.

For each fixture row, the interpreter replays exported witness programs and checks their
witness cells and assertions. For SP1-anchored rows it also applies the symbolic row map and
compares the complete result with SP1’s actual trace. These are executable tests; they do not
prove the serializer, interpreter or lowering correct.

## Run

```sh
cargo test --locked --manifest-path rust/witgen-interp/Cargo.toml
scripts/run_interp_diff.sh
scripts/run_interp_diff.sh --regen
scripts/run_interp_diff.sh --chip Add --verbose
```

Regeneration requires the full Lean test library to be built. A mismatch reports the chip,
fixture row and cell. Rust comparisons are currently opt-in; the integration migration will
make the direct-export comparison a locked Cargo CI check.

## Temporary vendoring

This repository owns the interpreter source. The pinned SP1 extraction branch also contains a
vendored copy under `crates/core/compiler/witgen-interp/`, allowing its standalone conformance
package to run without this checkout. `scripts/run_sp1_conformance.sh` checks the pin and byte
agreement before invoking that package. Keep the two copies synchronized while this evidence
remains live; retire both when the direct-export comparison replaces their coverage.
