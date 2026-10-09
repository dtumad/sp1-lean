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

The comparison crate uses release optimization level 1 to bound generated-code compiler memory;
dependency crates retain their normal release settings. CI logs the export step's time and peak memory.

The runner checks two byte-identical generations under `.lake/ensemble-export/`. Cargo compiles
that output and exercises two boundaries:

- The fixed-membership ensemble uses verifier-fixed columns and Clean's scheduler. Generated cells
  match Lean; backend proofs accept both allowed values and reject forged membership, changed public
  values, rows and table shapes. Test FRI parameters are not deployment security parameters.
- Production ADD, LoadByte, Bitwise, Lt, ShiftLeft, ShiftRight, Branch, Mul and DivRem components use the same comparison harness:

  | Component | SP1 event / padding rows | Column mutations | Cases |
  | --- | --- | --- | --- |
  | ADD | 81 / 15 | 396 | Carries, wraparound, operand boundaries |
  | LoadByte | 258 / 30 | 987 | LB/LBU, all eight offsets, sign extension, address boundaries, negative immediates, cross-window memory timestamps |
  | Bitwise | 612 / 28 | 5,661 | XOR/OR/AND, register and immediate forms, signed immediate boundaries, byte/limb/word boundaries, zero padding |
  | Lt | 468 / 12 | 4,884 | SLT/SLTU, register and immediate forms, equal operands, each differing limb, sign boundaries, zero padding |
  | ShiftLeft | 2,596 / 28 | 12,090 | SLL/SLLW, every shift amount, register and immediate forms, ignored upper shift bits, limb placement, word sign extension, nonzero padding powers |
  | ShiftRight | 6,136 / 8 | 27,531 | SRL/SRA/SRLW/SRAW, every shift amount, register and immediate forms, ignored upper shift bits, sign fill, word truncation/sign extension, nonzero padding powers |
  | Branch | 9,720 / 8 | 36,585 | All six opcodes, taken/fallthrough, equal operands, signed boundaries, negative/zero offsets, PC carries, `x0` reads, zero padding |
  | Mul | 605 / 3 | 5,166 | All five variants, signed and unsigned high products, word sign extension, operand boundaries, zero padding |
  | DivRem | 968 / 24 | 24,354 | All eight variants, division by zero, signed overflow at both widths, word truncation, DIVU padding |

  Generated witnesses are checked against SP1's live trace generator. Direct field evaluation compares local
  constraint satisfaction and complete interaction multisets, including mutations. Repeated messages
  and zero multiplicities are retained. Both Cargo configurations, with and without `mprotect`, run
  these **supervisor-mode** comparisons with trusted-program public values.

The instruction fixture has open external buses. A test-only `Program` adapter uses Clean's runtime
to construct the local row without scheduling those buses; the unadapted program is checked to
reject an active row without providers. This is not a full-ensemble acceptance or completeness test.
The layout adapters move selectors first and witnessed cells last; LoadByte, Bitwise, Lt, ShiftLeft,
ShiftRight, Branch, Mul and DivRem use offsets from SP1's actual column structures. The selector
adapters also check that their mappings are complete
permutations of their 51, 44, 65, 69, 45, 82 and 246 cells, including malformed selectors. Channel adaptation
reverses Byte, Memory and Program signs to match Clean's provider-to-consumer guarantee direction.

The default `inventory` feature retains the independent inventory checks. `clean-export` enables
the backend fixture alone; `instruction-export` also enables the live SP1 instruction comparison.

The Lean semantic profile and existing migration evidence remain on their separately recorded
revision until instruction comparisons and the semantic review pass.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track remaining instruction and provider coverage in [#28](https://github.com/dtumad/sp1-lean/issues/28)
and [#29](https://github.com/dtumad/sp1-lean/issues/29).
