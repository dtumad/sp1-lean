# Released SP1 comparison

This crate reads the installed AIR inventory directly from pinned SP1 v6.9.0 Rust sources.
Those sources provide the independent reference for generated native artifacts.

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
actual installed 95-component assembly; the full audit runs this check. The Cargo inventory tests
independently authenticate the snapshots against released Rust source. No generated Lean registry
serves as the Rust reference.

The inventory checks establish layout drift only. The instruction export suite also compares the
complete native opcode alphabet with every constructor and discriminant of the released Rust enum,
including unsupported instructions. This replaces the legacy Rust-to-Lean opcode-table parser.
Fresh Clean Rust is compiled against the backend
pinned to the same revision as the Lean emitter and compared with SP1:

```sh
python3 scripts/check_ensemble_export.py
```

Component comparisons use release optimization level 1. The runner compiles the large installed
assembly test binaries one at a time at level 0, with release debug assertions still disabled; this
bounds peak compiler memory and avoids expensive optimization of repeated complete-assembly instances. Both feature configurations run
every test, and dependency crates retain their normal release settings. CI logs the export step's
time and peak memory. These fixture settings do not measure optimized application performance.

The runner builds the `ensembleExport` Lake executable and uses it for two byte-identical
generations under `.lake/ensemble-export/`, then refreshes
the owned `compile-inputs/` directory without rewriting unchanged files. Cargo can reuse those
inputs across runs; fresh artifacts and provenance stay in separate run directories. Concurrent
runners are rejected before either can change the shared inputs. Comparisons cover these boundaries:

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

- The syscall instruction, guarded instruction and installed host-call wrapper use the same
  exporter/runtime. Eighty-five released events and eleven padding rows cover all eight native
  codes, every commit slot, canonical field-sized exits, full-word arguments and clock/PC carries;
  18,720 column mutations compare constraints, public bindings and every shared interaction.
  Public-value mutations bind the exit, flags and selected digest cells. Composed tests reject
  upper-word aliases and precompile dispatch, check WRITE's x12 read and retain inactive messages.
  Both configurations check supervisor mode; the optional syscall trap cell is explicitly zero.
  Weighted public queries preserve the complete bitmap, including on inactive rows. Sixteen
  inactive cases cover empty, unit, multi-hot, non-Boolean and cancelling weights, with public
  and cached-result mutations. The previous empty-bitmap drift is a passing regression; these
  finite comparisons do not establish arbitrary-row public equivalence. Host-handler effect coverage is
  described below; general active-host assembly generation remains open.

- HALT, constrained-replay ENTER, sixteen commitment handlers and two bank terminals compare
  their generated rows and complete ledgers with Lean references. Released SP1 execution and
  shard construction supply the control results, commit events and final banks. The comparison
  covers every slot and value boundary, repeated writes, literal per-call receipts, invalid
  clocks/arguments and source-backed Byte/Range membership. The unadapted components must reject
  open buses. Guarded commitment rows retain zero-multiplicity padding occurrences; terminals
  remain real boundary rows. Mutable bank history is separate from the immutable statement.
  A released-shard regression rejects earlier differing declarations despite operational success.

- Empty/nonempty HINT_LEN and HINT_READ handlers compare complete rows and ledgers with native
  constructor references. Released execution supplies repeated length observations, queue pops,
  return values and padded memory writes across byte, word and limb boundaries. Tests match the
  resulting node, final-word and cursor receipts and reject malformed calls/clocks/spans. These
  handler checks alone do not establish physical Memory coverage or whole-assembly acceptance.

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
  three-request fixtures pad to four rows and compare complete Lean/Rust rows and ledgers, including repeated requests,
  unused intervals, address bounds and empty ROM; backend tests reject forged endpoints, counts,
  public values and witness cells. Clean's ordinary demand scheduler receives each public address;
  the production circuit generates interval witnesses using the shared memory selector. No private
  inputs or fixture-specific interval programs are needed. Boolean activity gates assertions and
  multiplicities while preserving both physical interaction occurrences on padding rows. Backend
  checks reject invalid activity, missing active requests and activated padding, and accept arbitrary
  child cells on disabled rows. General host-assembly generation remains open. This is native ROM protection, not released SP1 runtime
  `mprotect` semantics.

- Immutable hint sources use verifier-fixed node/word payloads on their existing channels.
  Independent Rust inputs reconstruct reverse allocation order, tail links, lengths, little-endian
  words and mandatory final padding. Closed fixtures compare every physical row and ledger
  occurrence, generation failures and raw acceptance, including repeated requests, unused sources
  and empty queues. Backend tests reject changed public fields, counts and fixed heights. These
  are native source-queue tests; complete SP1 host execution remains outside their scope.

The installed 95-component assembly is lookup-free. Branch, empty, stopped, 16/24-byte HINT_READ,
active HALT, commitment programs and mixed ordinary/host programs use the same physical inventory
and Clean hint-table inputs.
Comparisons check every Lean/Rust row and ledger occurrence, fixed heights, empty positions and
complete balance. Fresh backend proofs test public mutations, missing terminals, fabricated
receipts, changed provider counts and non-Boolean or activated padding. Fixed declaration columns
are reconstructed independently from released shard public values; they are not mutable trace cells.

The immutable commitment statement supplies a sixteen-row fixed provider and public assertions.
The 58-cell header preserves the previous 48 positions and appends deferred words and flags.
Every active declaration agrees with the statement; final mutable banks record only executed
updates. Three identical declarations pad to four physical rows. Partial declarations and all
sixteen slots followed by HALT exercise register aliases, bank histories and target changes.
Released executor events, final banks, shard public values and syscall AIR supply an independent
comparison. Zero/wide/maximal field exits cover active HALT without a duplicate padding Exit.
Stopped segments also reject altered digest carriers. Flags imply neither declaration occurrence
nor all-slot coverage. A conflicting overwrite remains executable but unprovable for one statement.
The padding-only Exit row retains unused clock freedom; tests accept that freedom and reject
activating its forbidden HALT flag.

HINT_READ cases close Memory, queue and cursor ledgers, including mandatory final zero words and
three-to-four padding in boundary, target-check and nonfinal transfer rows. Repeated HINT_LEN
observations surround two overlapping reads with empty, byte-tail and aligned inputs. Independent
released prefixes check intermediate transfers as well as the final RAM state. ENTER executes its
real unconstrained/rollback path and compares the constrained replay with the native assembly.

The ordinary fixture combines ADDI, repeated SD/LD and taken/untaken BEQ, with aliased registers.
Its full run, prefix, suffix and empty endpoint compare complete Memory access occurrences with
released records, including displaced timestamps after resetting the authenticated local boundary.
Cuts agree on their public clock/PC endpoints. These finite fixture constructors use the production
access compiler and semantic host steps; they are neither an interpreter nor a total Sail compiler.
General generation completeness and WRITE/VERIFY installation remain open.

The experimental Clean pin adds message
predicates and indexed preallocated handlers to its existing scheduler. The provider fixtures exercise these APIs;
general whole-assembly generation still needs its own routing, padding, data and completeness contracts.
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

`symbolic_arithmetic_export` checks ADD, ADDI, ADDW, SUB and SUBW algebraically. Upstream symbolic
expressions bound total degree by three; a complete interpolation grid determines the constraint
polynomials after each AIR independently enforces its zero-register column. Independent released
layout offsets define the permutation. Constraint systems agree up to nonzero scaling and
repeated/zero equations, and every affine interaction occurrence agrees on a determining basis.
The grids contain 6,545 / 4,960 / 8,436 / 6,545 / 5,984 points respectively. Both configurations
check the supervisor profile; unexpected degree, public dependencies or expression forms fail.
Fault controls run for every family. This trusts Rust evaluators, bounds and adapters, without
an expression interpreter or formal lowering claim.

The remaining instruction families retain finite assurance. In addition to individual column
mutations, source-evaluator-guided walks change multiple columns and retain alternate accepted
rows. A second walk holds all prover inputs fixed to exercise alternate valid witnesses where
available. Every candidate, including rejected ones, compares complete interaction multisets.
This is broader adversarial coverage, not universal row equivalence.

The same harness compares both installed bump tables, including every padding row and mutations
of every column with three deltas. MemoryBump covers 24 refresh/bump events and eight padding rows,
read/write origins, register boundaries, 24/32/48-bit timestamp boundaries and unchanged old values.
StateBump covers seven events and 25 padding rows, clock carries and one/two-limb PC carries.
Separate padding checks preserve SP1's gated memory comparison and ungated PC-carry equations.
All bump cells are inputs: these tests compare the supplied rows, local constraints and complete
open-bus ledger, not a native execution-to-row generator.

All six native byte providers are compared with SP1's actual `ByteChip` preprocessed trace and
AIR over all 65,536 operand pairs, each at multiplicities `0`, `1`, `2` and `p-1`. The full six-entry
message multiset is compared without dropping zeros or combining repeated MSB keys. Native rows
prove membership with polynomial constraints; SP1 authenticates its fixed table, so their physical
layouts and local constraint lists are intentionally different. Boundary-pair mutations check
every native column with three deltas. Out-of-range operands must fail even at zero multiplicity;
zero padding balances, and unmatched nonzero provider rows fail. These tests also run with
`mprotect` enabled; they establish no additional mode semantics or ensemble count bounds.

All 17 installed fixed-width Range providers are compared with every row of SP1's 131,072-row
preprocessed Range table and its AIR at the same four multiplicities. The two `(0, 0)` physical
occurrences are retained. Boundary values exercise every native column, out-of-range values reject
even at count zero, and unmatched nonzero counts cannot balance. The released count generator is
also checked on sparse boundary requests. As with Byte, native bit-decomposition rows and SP1's
fixed rows have different physical layouts.

The [archived provider experiments](https://github.com/dtumad/sp1-lean/pull/153) compare unified
and verifier-fixed alternatives with the installed specialized providers. Their source and timing
transcripts remain in the linked checkpoints; the routine checks cover the installed library.
Proving and verification currently rebuild preprocessing, so those measurements include setup.

The instruction fixture has open external buses. A test-only `Program` adapter uses Clean's runtime
to construct the local row without scheduling those buses; the unadapted program is checked to
reject an active row without providers. This is not a full-ensemble acceptance or completeness test.
The layout adapters move selectors first and witnessed cells last. They use offsets from SP1's
actual column structures and check complete permutations; ADD retains its simple rotation.
No generated row-map JSON supplies the reference layout. Channel adaptation
reverses Byte, Memory and Program signs to match Clean's provider-to-consumer guarantee direction.

The default `inventory` feature retains the independent inventory checks. `clean-export` enables
the backend fixture alone; `instruction-export` also enables the live SP1 instruction and byte-provider comparisons.

The native semantic restrictions are independent of extraction. The reverse-extraction pipeline
is retired; its evidence and original provenance remain in Git history.
Neither inventory coverage nor a statically optional carrier establishes mprotect correctness.

Track remaining provider, ensemble and mode coverage in [#28](https://github.com/dtumad/sp1-lean/issues/28)
and [#29](https://github.com/dtumad/sp1-lean/issues/29).
