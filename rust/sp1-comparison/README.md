# Released SP1 comparison

This crate reads the installed AIR inventory directly from SP1 v6.9.0. Its Git dependency
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

The reviewed [coverage record](inventory/coverage.json) classifies every released layout and every
installed native component. The same source layout has the same status in both configurations;
additional user layouts remain explicitly outside the native profile. Ordered native entries retain
component occurrences, widths and legacy lookup occurrences. Evidence is grouped to avoid duplicating
proof paths and scope limits. `component` means built-in export with a Rust comparison;
`subcomponent` means only part of that group's assembly is exported; `none` remains an open gap.
The comparison kind distinguishes released-SP1 agreement tests from native-only backend tests;
the latter do not claim agreement with a released layout sharing that group.

`scripts/check_release_surface.py` checks this record against both Rust inventory snapshots and
the target revision in provenance. After the full test build, its `--native` option also reads the
actual installed 94-component assembly; the full audit runs this check. The Cargo inventory tests
independently authenticate the snapshots against released Rust source. No generated Lean registry
serves as the Rust reference.

The inventory checks establish layout drift only. Fresh Clean Rust is compiled against the backend
pinned to the same revision as the Lean emitter and compared with SP1:

```sh
bash scripts/check_ensemble_export.sh
```

The comparison crate uses release optimization level 1 to bound generated-code compiler memory;
dependency crates retain their normal release settings. CI logs the export step's time and peak memory.

The runner checks two byte-identical generations under `.lake/ensemble-export/`. Cargo compiles
that output and exercises these boundaries:

- The fixed-membership ensemble uses verifier-fixed columns and Clean's scheduler. Generated cells
  match Lean; backend proofs accept both allowed values and reject forged membership, changed public
  values, rows and table shapes. Test FRI parameters are not deployment security parameters.
- Source-register authentication pairs the production sparse Memory consumer with all 32 fixed
  membership rows. Forty cases cover every register, repeated requests, altered limbs and forged
  indices. Rust independently computes the snapshot and complete Memory/membership ledgers;
  backend tests mutate each public field, every sparse cell and all counts. An unused-provider
  ensemble retains all 32 zero-count occurrences. This tests the native arbitrary-snapshot
  contract, not agreement with SP1's boot-only all-zero register table. Both Cargo configurations
  run these checks, without claiming additional mprotect semantics.
- Target-register authentication checks complete final receipts on a separate membership
  channel. Its 42 cases cover every register, repeated receipts, forged values/indices and
  malformed upper address limbs. Rust reconstructs both clock limbs and the full receipt ledger;
  backend tests bind every public field and mutate every sparse cell and count in both
  directions. Generation can succeed for an assertion-invalid address, which the backend must
  reject. An unused target provider retains all 32 zero-count rows. These are native boundary
  tests, without a claim of SP1 execution or cryptographic security.
- Static providers cover empty, singleton, uneven, duplicate and all-zero tables: 80 request
  pairs and five unused-provider cases. Rust reconstructs payloads, eligibility flags, padding
  and counts from independent input lists. Backend checks bind public requests and reject
  mutations of every count, including duplicate and padding rows. A fixed eligibility tag keeps
  real zero requests distinct from inactive rows without a custom scheduler.
- RAM byte/word reads, source providers and target validators are exported through Clean. Rust
  independently checks sparse bytes, carries, first-entry precedence, native bounds, malformed
  limbs and the full generated rows/ledgers against Lean. Closed source/target interval-provider
  ensembles bind every public endpoint and byte; backend mutations cover all counts and padding.
  These are native RAM tests, not agreement with SP1's global-memory digest machinery.

- The full-register syscall guard exports as arithmetic AIR with six shared witness products,
  eleven assertions and maximum degree three. Rust checks every 16-bit low code against the
  eight selected variants of SP1's enum, compares twelve Lean reference rows, rejects upper-limb
  aliases and nonboolean activity, and mutates every product on active and padded rows. This
  checks the stricter native code profile; host effects remain separate obligations.

- The installed fixed Program provider retains sixteen verifier-owned instruction fields and one count.
  Tests compare SP1's preprocessing, count generator and AIR, including unused instructions,
  first-row padding and zero counts. Backend checks bind every instruction field and reject
  changed counts, while allowing count redistribution among duplicate padding keys. The empty
  native inventory has one inert row. Separate native tests cover unordered sparse addresses
  across all PC limbs using a first-match index in Clean's witness IR and its checked routing. The sparse native ROM contract
  is broader than the contiguous SP1 fixture. Clean requires
  power-of-two heights, so larger source comparisons must request a matching fixed SP1 shape.

- Native write permissions use their production request circuit and a verifier-fixed interval
  provider. Independent Rust expectations derive writable bytes from literal ROM PCs. Closed
  two-request fixtures compare complete Lean/Rust rows and ledgers, including repeated requests,
  unused intervals, address bounds and empty ROM; backend tests reject forged endpoints, counts,
  public values and witness cells. Clean's preallocated witness IR selects intervals from the
  private address inputs, which are bound to public requests by the complete ledger. This is
  native ROM protection, not released SP1 runtime `mprotect` semantics. Address-driven demand
  generation for the full machine remains open.

Two legacy lookup meanings still block full export: hint nodes and hint words. The experimental Clean pin adds message predicates and indexed
preallocated handlers to its existing scheduler. The provider fixtures exercise these APIs;
whole-assembly generation still needs its own routing, data and completeness contracts.
The component tests use the existing row adapter and independently check external interactions;
they do not establish complete ensemble balance.

- All 25 production instruction components use the same comparison harness:

  | Component | SP1 event / padding rows | Column mutations | Cases |
  | --- | --- | --- | --- |
  | ADD | 81 / 15 | 396 | Carries, wraparound, operand boundaries |
  | ADDI | 55 / 9 | 5,760 | Signed immediate boundaries, carries, wraparound |
  | ADDW | 176 / 16 | 20,736 | Register/immediate forms, truncation and sign extension |
  | SUB | 121 / 7 | 12,672 | Borrow chains, wraparound, operand boundaries |
  | SUBW | 121 / 7 | 12,288 | Borrow chains, word truncation and sign extension |
  | LoadByte | 258 / 30 | 987 | LB/LBU, all eight offsets, sign extension, address boundaries, negative immediates, cross-window memory timestamps |
  | Bitwise | 612 / 28 | 5,661 | XOR/OR/AND, register and immediate forms, signed immediate boundaries, byte/limb/word boundaries, zero padding |
  | Lt | 468 / 12 | 4,884 | SLT/SLTU, register and immediate forms, equal operands, each differing limb, sign boundaries, zero padding |
  | ShiftLeft | 2,596 / 28 | 12,090 | SLL/SLLW, every shift amount, register and immediate forms, ignored upper shift bits, limb placement, word sign extension, nonzero padding powers |
  | ShiftRight | 6,136 / 8 | 27,531 | SRL/SRA/SRLW/SRAW, every shift amount, register and immediate forms, ignored upper shift bits, sign fill, word truncation/sign extension, nonzero padding powers |
  | Branch | 9,720 / 8 | 36,585 | All six opcodes, taken/fallthrough, equal operands, signed boundaries, negative/zero offsets, PC carries, `x0` reads, zero padding |
  | JAL | 40 / 24 | 5,952 | Signed offsets, PC carries, discarded links, zero padding |
  | JALR | 321 / 31 | 36,960 | Signed immediates, cleared low bit, address wraparound, `x0` sources/destinations, zero padding |
  | UType | 80 / 16 | 8,928 | LUI/AUIPC, signed upper immediates, PC carries, discarded writes |
  | LoadHalf | 130 / 30 | 21,120 | LH/LHU, aligned offsets, sign extension, address and timestamp boundaries |
  | LoadWord | 66 / 30 | 12,672 | LW/LWU, aligned offsets, sign extension, address and timestamp boundaries |
  | LoadDouble | 17 / 15 | 3,744 | LD, full words, address and timestamp boundaries |
  | LoadX0 | 471 / 9 | 69,120 | All seven load variants with discarded results |
  | StoreByte | 385 / 31 | 62,400 | SB, all byte offsets, surrounding-byte preservation |
  | StoreHalf | 193 / 31 | 30,240 | SH, aligned offsets, surrounding-halfword preservation |
  | StoreWord | 97 / 31 | 16,896 | SW, both aligned offsets, surrounding-word preservation |
  | StoreDouble | 49 / 15 | 7,488 | SD, full-word replacement |
  | Mul | 605 / 3 | 5,166 | All five variants, signed and unsigned high products, word sign extension, operand boundaries, zero padding |
  | DivRem | 968 / 24 | 24,354 | All eight variants, division by zero, signed overflow at both widths, word truncation, DIVU padding |
  | AluX0 | 451 / 29 | 48,960 | All 29 ALU variants, legal register/immediate forms, discarded writes |

  Generated witnesses are checked against SP1's live trace generator. Direct field evaluation compares local
  constraint satisfaction and complete interaction multisets, including mutations. Repeated messages
  and zero multiplicities are retained. Both Cargo configurations, with and without `mprotect`, run
  these **supervisor-mode** comparisons with trusted-program public values.
  Every family includes padding and three mutation deltas per tested column. ADDI, ADDW, SUB,
  SUBW, JAL, JALR, UType, AluX0 and memory components other than LoadByte mutate every row;
  the remaining components use selected boundary rows.

All six native byte providers are compared with SP1's actual `ByteChip` preprocessed trace and
AIR over all 65,536 operand pairs, each at multiplicities `0`, `1`, `2` and `p-1`. The full six-entry
message multiset is compared without dropping zeros or combining repeated MSB keys. Native rows
prove membership with polynomial constraints; SP1 authenticates its fixed table, so their physical
layouts and local constraint lists are intentionally different. Boundary-pair mutations check
every native column with three deltas. Out-of-range operands must fail even at zero multiplicity;
zero padding balances, and unmatched nonzero provider rows fail. These tests also run with
`mprotect` enabled; they establish no additional mode semantics or ensemble count bounds.

The uninstalled unified Byte/Range prototype is compared with every row of SP1's actual Byte
and Range preprocessing and AIR, at the same four standalone count classes. The Range comparison
retains both copies of its zero-width row. Closed tests use Clean's ordinary scheduler, check full
Lean/Rust rows and ledgers, and exercise repeated requests, all widths, 64/65 distinct requests,
malformed inputs, selectors, counts, padding and public binding. The installed providers remain
the baseline; no full-machine or additional mode coverage follows from this prototype.

A second uninstalled provider experiment matches SP1's physical preprocessing: 65,536 Byte
rows (seven fixed columns and six counts) and 131,072 Range rows (two fixed columns and one
count). Kernel proofs establish membership and canonical index coverage. Rust compares every
fixed cell and interaction with released preprocessing/AIR, compares honest counts with SP1's
trace generators, and checks complete generated rows against Lean. Duplicate keys remain valid
at every physical occurrence; canonical indexing is an honest-generation choice.

The cost fixture compares the 23 specialized providers with message routing, the unified provider,
and these two fixed tables. It retains the nine small workloads and adds mixed distinct and
repeated-key workloads at 1,024, 16,384 and 65,536 requests. Large cases use the same runtime
request table in all layouts; public binding is tested separately by the small fixtures. All
layouts use Clean's generator and Plonky3's benchmark FRI parameters, with two threads, one
warmup and three samples. Prove/verify times include preprocessing on every call: the backend
currently has no reusable-preprocessing API. Reports also record committed cells, occurrences,
source bytes, JSON proof bytes and per-process peak RSS. JSON size is not a wire-format size,
and this profile makes no whole-system security claim.

Run `python3 scripts/measure_byte_providers.py --artifacts <export-dir>
--binary <unified_byte_export-test-binary>` to repeat measurements after fresh export.
Artifacts stay under the ignored `.lake/ensemble-export` tree. Installation and upstream
adoption require review of the complete costs and proof obligations.

The instruction fixture has open external buses. A test-only `Program` adapter uses Clean's runtime
to construct the local row without scheduling those buses; the unadapted program is checked to
reject an active row without providers. This is not a full-ensemble acceptance or completeness test.
The layout adapters move selectors first and witnessed cells last. They use offsets from SP1's
actual column structures and check complete permutations; ADD retains its simple rotation.
No generated row-map JSON supplies the reference layout. Channel adaptation
reverses Byte, Memory and Program signs to match Clean's provider-to-consumer guarantee direction.

The default `inventory` feature retains the independent inventory checks. `clean-export` enables
the backend fixture alone; `instruction-export` also enables the live SP1 instruction and byte-provider comparisons.

The native semantic restrictions are independent of extraction. Existing reverse-extraction
evidence retains its original provenance until replacement coverage allows the pipeline's deletion.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track remaining provider, ensemble and mode coverage in [#28](https://github.com/dtumad/sp1-lean/issues/28)
and [#29](https://github.com/dtumad/sp1-lean/issues/29).
