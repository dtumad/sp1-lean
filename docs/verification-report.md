# Formal Verification of SP1 Core Instruction AIRs and Native AIR-to-Execution Refinement in Lean — Technical Report

*sp1-clean-native — a Clean-native, semantically-specified verification of SP1's RISC-V chips.*
*Snapshot: 2026-09 (repository tree at this document's commit; Lean v4.32.2 + Sail v5; SP1 semantic pin
`v6.4.0`).*

> **Line-number caveat.** Declarations are cited by name and file; line numbers appear only where
> stable. Every cited repository path and a release-critical set of cited declaration names are
> mechanically checked against the tree at the snapshot commit (see §13); quoted signature *text* is checked by review, not by
> machine. If a quote and the tree ever disagree, the tree is authoritative.

## 1. Executive summary

This repository contains a machine-checked verification, in the Lean 4 proof assistant, that
**each of the 25 instruction chips of SP1 v6.4.0's supported Core profile soundly implements the
official RISC-V instruction-set semantics** — proven against the Sail-generated RV64 model and
composed into a machine-level soundness theorem over a native 55-table ensemble with explicitly
disclosed boundary premises (§8; the exact-upstream refinement boundary is §8.3). The
verification is built on the public
[Clean](https://github.com/Verified-zkEVM/clean) zkVM DSL and is structured so that every claim is
either a kernel-checked theorem, a mechanically enforced pin, or an explicitly named open
obligation.

The deliverables:

- **D1 — Native chip formalization.** All 25 supported instruction chips (the RV64IM ALU,
  control-flow, and memory core) are implemented as Clean `GeneralFormalCircuit`s with semantic
  specifications, plus 30 provider/boundary tables, forming the 55-table `sp1Ensemble`
  (`SP1Clean/Soundness/SP1Ensemble.lean`). The provider suffix is six Byte-op tables, 17 Range
  tables for widths `0..16`, Program, MemoryInit, MemoryFinalize, MemoryBump, StateBump, Halt, and
  SyscallInstrs. Active SyscallInstrs rows remain excluded by `SyscallTableInactive` (§8.1).
  All 17 widths are needed: honest shift rows emit live Range requests outside the former
  `8/13/14/16` subset. The Halt table is this repository's own — it implements the `HALT` arm of
  SP1's `SyscallInstrsChip`, whose other arms and global syscall bus the supported profile
  excludes — and it is the one table without a faithfulness anchor (§8.2).
- **D2 — Per-chip soundness, completeness, and ISA refinement.** Every chip carries closed
  soundness *and* completeness proofs against a semantic `Spec`, and a Sail bridge (`advance`)
  showing its rows realize genuine steps of the official RV64 interpreter.
- **D3 — Whole-chip Rust faithfulness.** For each chip and every extracted Rust row, a
  `ChipFaithful` theorem reconstructs the canonical native physical row and proves the hand-built
  native circuit's complete constraint system is *bidirectionally equivalent* there to the complete
  `assertZero` list extracted from SP1's Rust `Air::eval`; accepted rows also have equal interaction
  multisets up to permutation (§4). This does not quantify over arbitrary physical native
  assignments outside the reconstruction codec's image.
- **D4 — Machine-checked bus grounding.** The meaning of the inter-chip buses (state, program,
  memory, byte) is *derived* inside Lean from Clean's proved balance theorem plus per-chip
  lemmas and the named boundary premise of §8.1 — there are no paper-justified bus axioms (§6).
  The public `supported_core_native_grounding` endpoint returns the initial boundary facts and the
  full grounding record, including its proved `finalStateTruth` and `memoryFinalizeTruth`; the
  local-execution capstone is now visibly a projection of this reusable result.
- **D5 — The headline theorem.** `supported_core_native_sound`
  (`SP1Clean/Soundness/AIR.lean`): every constraint-satisfying, channel-balanced witness of the
  55-table ensemble, with an explicit boundary premise, yields a genuine finite,
  normally-retiring run of the official (SP1-configured, §3.2) Sail RV64 interpreter — either
  between the public program-counter/clock endpoints, or ending in a genuine `SP1Halted` state
  whose `a0` is the committed exit code, with the AIR's own Exit-channel algebra deciding which
  (§8.2) — and with no machine-model parameter (§8). One corollary,
  `supported_core_boot_to_halt_single_shard`, adds a boot boundary and states the first
  whole-program fact: entry point with zeroed registers to a halting state carrying the committed
  exit code, on a single shard.
- **D6 — Conformance testing against the real prover.** A dump-anchored pipeline reconstructs
  every event row of all 25 chips from the circuits' own witness generators and matches it
  cell-for-cell against full trace matrices dumped from SP1's actual Rust prover at SP1's field,
  with an independent Rust interpreter differential on top (§9). **Scope of that claim:** it is a
  *row/witness-generation* agreement, not a claim that every dumped row is a decoded-program
  execution row. The W4 completeness rollout surfaced a concrete instance: `export/sp1dump/
  UType.dump.json` contains rows whose `op_b` is `imm << 12` *without* the 64-bit sign extension
  (e.g. `0xFFFFF000`). Such a row cannot come from a decoded instruction — SP1's own
  `Instruction::encode` asserts `validate_sign_extension(op_b >> 12, 20)` on the UType branch — and
  it does not satisfy `UTypeChip.ProverAssumptions`' decode conjunct
  (`toBitVec64 op_b_imm = RV64.lui (immOf adapter)`). This is consistent rather than contradictory:
  SP1's UType AIR genuinely does not constrain the high limbs, and the chip's contract already
  labels that relation a trace/program-ROM guarantee rather than an in-circuit one. The practical
  consequence is that such synthetic rows sit inside the row-level conformance claim and outside
  the semantic one.
- **D7 — A reproducible audit harness.** One script (`scripts/run_audit.sh`) re-derives the
  dependency pins, gates zero proof deferrals with an empty allowlist, and regenerates a
  per-theorem `#print axioms` census (§13).
- **D8 — Deterministic native ensemble completeness.**
  `supported_core_native_functionalCompleteness`
  (`SP1Clean/Soundness/NativeCompleteness.lean`) maps an admissible supported
  `Machine.EventExecutionTrace` to `SupportedCoreNativeRelation` with no proof argument in the map.
  It compiles all 25 instruction families, schedules State/Memory refreshes, constructs Memory
  boundaries, recounts Byte/Range/Program demand from the literal Clean ledger, and builds all 55
  tables plus the verifier row with the circuits' own generators. Constraints and all seven Clean
  channel balances are conclusions. Its explicit admissible source is still narrower than the
  shared bounded ordinary target: registry-wide event validity, initial-Memory content, physical
  Program-row projection, and actual interaction footprint remain named source facts (§7.4).
  Capacity alignment itself is closed by the paired bounded soundness/completeness API.
- **D9 — Extracted-to-native local ensemble artifact.** `SP1Clean/Composition/`
  composes D3 with the native side, which Alex Hicks's 2026-08 PR #110 review found were never
  joined inside Lean. From valid witnesses of the pinned execution and memory-boundary clusters,
  **a caller-supplied `CanonicalPreprocessedInventory`, plus named preprocessing, memory-boundary,
  and public-limb transport contracts**, it constructs all 55 native tables plus the verifier row
  and proves the complete local constraint system. Exact
  Byte/Range/Program multiplicities are recounted from the actual Clean interaction ledger of the
  verifier, 25 transported instruction tables, MemoryInit/MemoryFinalize, and both bumps rather than
  copied from the full 34-table cluster, whose counts include consumers omitted from this native
  slice. The raw exact Byte/Range/Program assertion lists are empty. `CoreAIR.PreprocessedBinding`
  only records the named matrix/PCS-opening premise, to be discharged by ArkLib; it proves neither
  row-local meaning nor provider selection. `PreprocessedProviderContract` is the explicit caller
  premise for that meaning. Source
  main multiplicities are not reused, and neither premise implies projected-key uniqueness or
  native-demand coverage. The selected
  inventory's carriers must be backed by their matching source matrix/Range-width block, while
  projected-key `Nodup` is an explicit inventory field and zero-demand raw keys may be omitted. The
  recount contract separately requires nonzero Byte/Program-key coverage, consumer nonpositivity,
  and `2 * count ≤ p`. `freshRowsByKey` is declarative/regression-only. PCS/program identity,
  State/Memory balance, and the semantic boundary remain separate and explicit. Exact
  access-permutation and
  exact-natural-balance→centered-integer lemmas are reusable infrastructure. `CoreArtifact` consumes
  an explicit provider-recount contract to derive Byte (including Range) and Program integer balance;
  `ExactNativeGlobalContract` retains all-channel count bounds, State/Memory integer balance, and
  semantic binding. When both are supplied, the artifact reaches D5 and Sail. No theorem jointly
  inhabits them with valid exact clusters. Deriving them across the named
  provider/public-boundary representation changes remains open, so exact-upstream refinement (§8.3)
  is still conditional (§12).

**The honest claim boundary, up front.** The proved statement is *existential and shard-local*:
it produces a Sail execution segment for one shard, whose initial state is characterized by the
provider-table binding rather than tied to an ELF-loaded boot state, and it consumes one
explicitly disclosed semantic premise (the provider/program binding) that is not yet derived from
the exact upstream system tables. D8's assembly source requires caller-supplied routing,
aggregate-count capacity, exact centered-integer balance, public equality, and boundary-binding
facts — exactly what a future generator-correctness theorem must establish. D9 assembles the full
local artifact under named transport contracts but
deliberately names, rather than assumes away, the remaining global interaction and semantic-binding
derivation. The
repository deliberately *reserves* — declares nothing under — the names `sp1_air_sound`,
`sp1_execution_sound`, and `sp1_verifier_sound`: the exact-upstream refinement exists only as an
honestly conditional combinator (`sp1_air_sound_of_obligations`) over a named, currently
uninstantiated proof bundle (§8.3), the cross-shard execution relation is specified but has no
soundness theorem, and no cryptographic/probabilistic verifier claim of any kind is made (that is
the planned ArkLib layer, §12). No theorem in the main library depends on `sorry`, on any project
axiom, or on `native_decide`.

## 2. System overview

### 2.1 What is being verified

SP1 proves RISC-V guest executions with a STARK whose Core stage commits, per shard, a
multi-table AIR: one table per instruction class (Add, Mul, LoadByte, …), system tables
(syscalls, memory bumps, global accumulation), and preprocessed tables (program ROM, byte table,
range table). Tables communicate over LogUp-style buses: a chip row *pulls* its operands (a
register read is a receive on the memory bus) and *pushes* its effects (the register write-back,
the next CPU state). The verifier checks each table's polynomial constraints plus the global
bus balance.

The verification target is SP1 at semantic revision
`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529` (`v6.4.0`), pinned in
`SP1Clean/FormalModel/CoreProfile.lean` (`sp1SemanticRevision`) and enforced end-to-end by the
extraction pipeline (§4). The supported profile is the exact 25-instruction-table slice of
upstream `RiscvAir::machine()`:

| Class | Chips |
|---|---|
| ALU / R-type | Add, Addi, Addw, Sub, Subw, Bitwise (XOR/OR/AND), Lt (SLT/SLTU), ShiftLeft (SLL/SLLW), ShiftRight (SRL/SRA/SRLW/SRAW), Mul (MUL/MULH/MULHU/MULHSU/MULW), DivRem (8 ops), UType (LUI/AUIPC) |
| Control flow | Jal, Jalr, Branch (BEQ/BNE/BLT/BGE/BLTU/BGEU) |
| Memory | LoadByte/Half/Word/Double, StoreByte/Half/Word/Double |
| x0 fast paths | AluX0 (any covered ALU op with `rd = x0`), LoadX0 (any load into `x0`) |

The only opcodes of SP1's 53-value opcode alphabet outside this profile are ECALL, EBREAK, and
UNIMP; they route to no chip on both sides (SP1's syscalls are ECALL-dispatched and handled by
the system tables and an explicit `SyscallHandler` boundary, §7.3). The routing table — including
the `rd = x0` dispatch split — is proved to partition the alphabet and has been independently
diffed against SP1's `tracing.rs` event emission, arm by arm.

### 2.2 Architecture: five pillars around a whole-chip boundary

The stable verification boundary is the **whole chip**, not individual gadgets:

```
Math/, Model/        general math + the SP1 substrate (Sail wrapping, buses, machine model)
Extracted/           auto-generated: complete Rust rows, assertZero lists, interaction lists
FormalModel/         the audit surface: Inputs + semantic Specs + relations (what is claimed)
Native/              hand-built Clean circuits (chips, operations, readers)
Proofs/, Faithful/,  soundness/completeness/Sail bridges; native↔Rust faithfulness;
Soundness/           the whole-machine grounding engine and the capstone theorems
```

Two design decisions distinguish this from transcription-style verifications:

1. **The Lean circuits are independent implementations, not transcriptions.** A native chip and
   SP1's Rust chip may decompose arithmetic differently; nothing requires per-gadget
   correspondence. The two are reconciled only at the whole-chip boundary by the `ChipFaithful`
   theorem (§4.3), which compares *complete* assertion systems and interaction multisets. This
   keeps proof-oriented circuit engineering (subcircuit reuse, witness design) free, while making
   the Rust-equivalence claim total rather than per-recognized-fragment.

   **One carve-out, and it matters for how much `ChipFaithful` is worth per chip.** For four
   operations the native own-assert lists are token-for-token transcriptions of the generated
   lists (Addw, Subw, and LtU's own-asserts; DivRem's own-assert tail). Where a list was
   transcribed, the faithfulness theorem is a *pin-drift tripwire* — it will catch the extracted
   list changing out from under us — but it is not independent cross-validation of that list,
   because both sides descend from the same text. Soundness content is unaffected either way: the
   semantic `Spec` is still proved from the list, so a transcribed list that were wrong would fail
   to prove the ISA property rather than pass silently. The distinction is about what the
   *faithfulness* theorem adds, not about what is proved.
2. **Specs are semantic, not structural.** A chip's `Spec` states what a row *means* — e.g. for
   Add, `is_real = 1 → toBitVec64 value = RV64.add (toBitVec64 op_c) (toBitVec64 op_b)` — never a
   restatement of its constraint list. The field is generic over primes, at three thresholds:
   `p > 2^17` for the chip layer, `p > 2^24` where Mul's column-sum bounds require it, and
   `p > 2^25` for the timed-grounding layer and the `supported_core_native_sound` capstone
   (`Fact (2 ^ 25 < p)` in `SP1Clean/Soundness/AIR.lean`; this is SP1's own memory-argument
   requirement — upstream `memory.rs` asks for a field larger than `2 · 2^24`, see the module
   docstring of `SP1Clean/Soundness/TimeExtraction.lean`). SP1's KoalaBear
   (`p = 2^31 − 2^24 + 1`) satisfies all three, and the conformance layer runs at exactly that
   field.

## 3. The Sail foundation

### 3.1 The model and the step relation

The ISA authority is the **official RISC-V Sail specification**, mechanically translated to Lean
(the `LeanRV64D` model, generated by the opencompl `sail-riscv-lean` pipeline). The repository
does not hand-write an ISA model; it wraps the generated interpreter:

```lean
-- SP1Clean/Model/Semantics/GuestProgram.lean
def SailStep (s s' : SailState) : Prop :=
  ∃ b : Bool, (try_step 0 false).run s = .ok b s'
```

`try_step` is the model's topmost entry point — interrupt dispatch, instruction fetch, decode,
execute, and PC commit — so no part of the interpreter is bypassed. Chains of steps
(`SailChain`), initial-state loading (`IsInitialState`), and the halt convention (`SP1Halted`:
PC at the halting ECALL with `x5 = HALT = 0` and the exit code in `x10`, matching SP1's Rust
syscall convention) are all defined over that single step relation. The two fixed `try_step`
arguments are audited benign: `step_no` feeds only trace strings, and `exit_wait` affects only a
hart-waiting arm that is dead under the configured active-hart state.

Instruction decoding is anchored to Sail: the typed program-ROM decoder used by the grounding
engine is anchored to the generated `ext_decode` (a `decodedInROM` fact yields
`(ext_decode w).run s = .ok i s`), with per-class round-trip lemmas — so opcode/funct field
extraction reaches the official Sail model. The new finite-image provider additionally uses an
executable parser whose uniform agreement with that decoder is proved (§7.2); integrating that
provider into the released machine theorem remains separate work.

### 3.2 The generated platform configuration: two keys, four value sites

SP1's runtime differs from a stock RV64 platform (no CLINT timer, no PMP, no external-interrupt
device). Rather than assuming these away per-proof, the repository builds on a `sail-riscv-lean`
snapshot **generated from pinned Sail sources with a checked-in SP1 platform configuration**
(`scripts/sail-config/`; provenance and pipeline in `docs/agents/sail-model-provenance.md`).
The semantic delta from the stock generated model is **exactly four platform-value sites across
two generated files** — the images of a two-key config. The two top-level values are
*disclosed* as `rfl` lemmas in `SP1Clean/Model/SailMemory.lean`; the remaining two sites are
`let`-bindings inside the generated `ValidateConfig` check (configuration validation only, not
on the execution path), visible in the generated source but not addressable as Lean lemmas:

```
plat_have_clint       = false   -- no core-local interruptor        (rfl lemma)
plat_have_sig         = false   -- no interrupt-generator device    (rfl lemma)
clint_supported       = false   -- ValidateConfig's CLINT check     (let-site in ValidateConfig)
sig_supported         = false   -- ValidateConfig's SIG check       (let-site in ValidateConfig)
```

The four sites are the images of two config keys (`platform.clint.supported`,
`platform.simple_interrupt_generator.supported`), and the generator reads each key everywhere it is
consumed. PMP is deliberately **not** configured: the model keeps upstream's 16 entries, and
"every entry is OFF" is carried as the state hypothesis `isValidMemConfig.h_pmp_off` instead —
visible in Lean rather than in the generation config. Nothing can falsify it, because SP1
implements no CSR instructions (its disassembler maps every `csrr*` to `unimp`).

The **two device keys are load-bearing, not a convenience**; the two PMP keys are weaker, and the
report states the difference rather than averaging over it (audited 2026-08-19). SP1's address
chips bound every access to `[2^16, 2^48)`, and the upstream CLINT window
`[0x0200_0000, 0x020C_0000)` and interrupt-generator window `[0x0C00_0000, 0x0C00_0020)` both lie
inside it. With the devices enabled a Sail access in either window routes to the device instead of
RAM, which makes the two `within_mmio_*` memory-bridge lemmas **false as stated** — they quantify
over address and width with no range side-condition — and the disjointness hypothesis that would
recover them is not derivable from SP1's AIR. Their fan-out includes the instruction-fetch
reduction, so it reaches every chip's `advance` obligation, not only the memory chips. SP1
implements neither device (`clint`/`mtimecmp`/`pmpcfg`/`pmpaddr` appear nowhere in its Rust tree),
so this is faithfulness as much as provability.

The PMP keys were **dropped** on this basis (2026-08-19): a stock 16-entry all-OFF PMP returns the
same answer at machine privilege, so every downstream conclusion held against stock. `run_pmpCheck_none`
was restated over the `h_pmp_off` hypothesis and reproved — the entry walk is discharged by an
invariant proved once by functional induction over `IntRange.forIn'`'s own well-founded measure, so
it is independent of the entry count.

The remaining platform configuration (machine privilege, disabled interrupts, HTIF off, the
single SP1 PMA region, …) is packaged as the `SailConfigured` invariant carried through every
execution statement, and `SailCodeMemoryCompatible` is the explicitly disclosed contract that
SP1's immutable program table and Sail's unified instruction/data memory agree on the code
region. (Compare Nethermind's A1–A4 assumptions for OpenVM, §11 — the same platform-shaping
concerns, handled there as per-proof hypotheses, here as a pinned config-generated snapshot plus
named invariants.)

### 3.3 What the Sail layer contributes to the trust base

The generated model's *platform hooks* remain external axioms of the Lean environment, disclosed
per-theorem by the axiom census. Seven of them concern the supported slice's own effects:
`plat_term_write`, the four LR/SC reservation operations (`load_reservation`, `match_reservation`,
`valid_reservation`, `cancel_reservation`), `get_16_random_bits`, and
`sys_enable_experimental_extensions`. (The Sail runtime's `print` is a total definition, not an
axiom.) None is given a nontrivial axiomatized *property*; they are opaque effects the supported
instruction slice does not semantically depend on.

A theorem whose target is the *complete* generated interpreter inherits the whole hook surface of
that target, including hooks the supported RV64IM path never executes, and the census discloses
this rather than pruning it. Measured at this snapshot,
`SP1Clean.Soundness.supported_core_native_sound` depends on 100 axioms: the three logical baseline
constants (`propext`, `Classical.choice`, `Quot.sound`), the seven platform hooks above, 67
`riscv_f*`/`riscv_i*`/`riscv_ui*` floating-point and integer-conversion hooks reached through
`try_step`'s full instruction dispatch, and 23 generated `bv_decide` proof constants inherited from
the shift/multiply/store bridge lemmas. See `docs/snapshots/axiom-ledger.md` for the per-class
reading and `docs/snapshots/axiom-census.txt` for the raw entry.

## 4. Extraction and Rust faithfulness

### 4.1 The pin-checked exporter

The "what does SP1 actually constrain" side enters Lean through `update_extracted.py`, which
drives SP1's own constraint compiler as a **trusted but heavily fenced oracle**:

- `SP1_DIR` must be the audited *extraction branch*: a checkout whose merge base with the
  semantic pin is exactly `f66b4bff5…` (the v6.4.0 tag), whose committed delta over the
  **semantic AIR sources** (the 25 chip files plus the shared memory-access columns carrier — the
  26-entry `EXTRACTOR_METADATA_FILES` set) is verified line-by-line to be reflection metadata only
  (`use sp1_derive` / `#[derive(...)`). Changes outside that surface are confined to an explicit
  trusted extractor/shape/tooling allowlist at the exact pinned commit; this includes `IntoShape`,
  the symbolic IR, the compiler, workspace metadata, and trace tooling, and is not a claim that
  those changes are semantically inert. The checkout's working tree is **clean**: every
  extraction change is an ordinary commit on the pinned branch, with no uncommitted-patch
  mechanism. Every gate is fail-closed (`SystemExit` before any file is written).
- The exporter emits, per table, the complete column structure, the ordered `assertZero` list,
  and the ordered interaction list — **never a Clean circuit**, so extraction cannot manufacture
  the proof's other side. The machine `Air::eval` and trace-population bodies remain unchanged
  except for line-checked reflection imports/derives. The pinned trusted tooling also changes
  shape selection (`IntoShape`) and symbolic-expression representation/emission; those hunks were
  reviewed as part of the extraction oracle, not proved to operate only after `air.eval`.
- A machine-shape manifest is extracted unconditionally and compared against the audited profile
  (34-table execution cluster, 6-table memory-boundary cluster, every main/preprocessed width,
  the 160-cell public-values block) before anything regenerates; `Extracted/Provenance.lean` pins
  the semantic revision and the extraction-branch revision (the semantic revision additionally
  tied to `CoreProfile` by an `rfl` theorem; the branch revision enforced by the regeneration
  gates).
- The instruction alphabet is extracted unconditionally too: `Extracted/OpcodeTable.lean` is the
  `Opcode` enum's variant-name → `#[repr(u8)]`-discriminant table (the value each chip commits on
  the Program bus), parsed textually out of `crates/core/executor/src/opcode.rs` **at the semantic
  pin via `git show`** (fail-closed on shape drift, independent of the exporter commits).
  The hand-maintained mirror `SP1Clean/Model/Opcode.lean` is cross-checked against it by the
  kernel-`decide` theorem `opcodeTable_matchesExtracted`
  (`SP1Clean/FormalModel/OpcodeTable.lean`), replacing what was previously a hand-verification.
- Regeneration is byte-idempotent: a full run at the pinned extraction branch reproduces all 60
  generated AIR modules identically (every `.lean` file under `SP1Clean/Extracted/` except the
  hand-written `ExtractionDSL.lean`; re-verified at this snapshot). The SP1 trace dumps behind the
  conformance layer (§9) are reproducible the same way (`scripts/update_sp1_dumps.sh --check`,
  byte-identity at the same pin).

The readable table profile is additionally hand-transcribed in
`FormalModel/CoreProfile.lean` and proved to match the generated manifest by `decide`
(permutation on names with equal widths) — and that transcription was independently re-checked
against upstream `riscv/mod.rs` name-by-name for this report.

The instruction-row width seam is kernel-checked too. `instructionOracleMainWidth` computes the
physical field count from each of the 25 generated Rust column structures, while
`supportedInstructionMainWidths` proves that every table in `CoreProfile.instructionTables` equals
the independently extracted manifest `mainWidth`. A generated struct field added without a matching
manifest/profile update now breaks a theorem rather than only an external measurement.

### 4.2 What "faithful" means here

For each chip, `Faithful/ChipOracle.lean` defines a `ChipOracle`: a bijective reconfiguration
between the typed native output columns and the extracted Rust columns
(`reconfigure`/`deconfigure` with proved round-trips — field-copy maps, closed by `cases; rfl`),
plus the extracted `assertZeros` and `interactions`. A separate `ChipRowCodec.assignment`
reconstructs the canonical input-first Clean physical row from those native output columns and the
committed prover data. The anchor theorem, quoted for Add:

```lean
-- SP1Clean/Faithful/AddChip.lean
theorem addChip_faithful :
    ChipFaithful (p := p) AddChip.Inputs AddChip.Columns Extracted.AddOracle.AddCols
      AddChip.circuit addChipRowCodec addChipOracle
```

where `ChipFaithful` demands, for **every** Rust row, on that reconstructed physical row:

1. *constraints*: SP1's complete `assertZero` list vanishes **iff** the native circuit's complete
   constraint system holds (bidirectional on the codec image — the native circuit neither weakens
   nor strengthens the Rust AIR there); and
2. *interactions*: on every locally-accepted row, the native circuit's active interaction multiset
   is a **permutation** of the Rust row's active interaction multiset (all four instruction buses, projected
   with multiplicities).

The quantifier is deliberately over extracted Rust rows. Six flag-hinted chips reconstruct a
codimension-one slice of the broader physical native assignment space (for example, setting
`is_real` to the selector sum). No released theorem claims the converse coverage statement for an
arbitrary native physical assignment; the exact-AIR transport uses the proved extracted → native
direction and lands in this image by construction.

`Faithful/SupportedMachine.lean` then ties the 25 anchors to the upstream profile: a list of
`ChipFaithfulnessAnchor`s carrying the actual theorems, with `rfl`/`decide` certificates that its
length, chip names (SP1's `MachineAir::name` strings), and table tags match the pinned
instruction-table profile. Adding, removing, or reordering a supported table breaks these
certificates in the same change.

### 4.3 The residual extraction trust and its mitigations

`ChipFaithful` compares native circuits against *extracted* lists; the step from Rust source to
extracted list is the trusted oracle. Three mitigations bound it: the fail-closed pin/branch/shape
fencing above; a manual spot re-derivation (for this report, the Add oracle was re-derived
symbol-by-symbol from `operations/add.rs` + `add.rs` — the 4-limb carry chain in its
`2^16`-inverse form, both `is_real` booleanity asserts, and the `(Range, value[i], 16, 0)` byte
sends match exactly); and the independent trace-conformance layer (§9), which exercises the same
rows against the real prover's output rather than the exporter's.

The formerly disclosed provenance gap here is closed: audit finding F-R-01 observed that the
dumper behind the original trace-conformance batteries existed at no pinned revision. The
successor pipeline (§9) dumps from `chip_traces`, an ordinary committed binary at the pinned
extraction branch; the committed dumps are reproducible byte-for-byte at the pin
(`scripts/update_sp1_dumps.sh --check`), and their `sp1Commit` is cross-checked against the
extraction pin by `scripts/check_pins.sh`.

## 5. Chip contracts: one worked example

### 5.1 Add, end to end

The Add chip illustrates the whole per-chip chain. Its **native circuit**
(`Native/Chips/AddChip/Defs.lean`) composes three true Clean subcircuits — the CPU-state block,
the R-type register reader, and the native add gadget (`Native/Operations/AddOperation/`, which
re-derives the u16-limb carry chain in-project) — and assembles the chip's own row type. Its
**Spec** (`FormalModel/Contracts/Chips.lean`, `AddChip` namespace) is a semantic statement over
that row:

```lean
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) ... : Prop :=
  ... Readers.RTypeReader.Spec { ... } ∧          -- the register-file discipline of the row
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    Word.toBitVec64 cols.add_operation.value
      = RV64.add (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))
```

with `op_b ↦ rs1`, `op_c ↦ rs2` projected from the reader's memory slots, and `RV64.add` the
riscv-lean reference function proved equal to the Sail `execute_RTYPE` ADD clause. Around this
Spec:

- **Soundness and completeness** (`Proofs/Chips/AddChip/Formal.lean`): the constraint system
  implies the Spec (assumptions: `True` — operand ranges are *derived* from the reader's bus
  pulls), and honest witness generation satisfies it.
- **The Sail bridge** (`Proofs/Chips/AddChip/Bridge.lean` + the chip's `advance` contract): a
  Spec-satisfying real row, wired to decoded program-ROM operands, realizes one step of the
  official interpreter. (Add is a `rd ≠ x0` chip — SP1 routes the `rd = x0` variant of every ALU
  opcode to the separate AluX0 table, whose own bridge proves the discarded write; chips that
  genuinely admit `rd = x0` rows, like Jal/Jalr, carry two proven bridge arms.)
- **Faithfulness** (`Faithful/AddChip.lean`, §4.2) and **conformance** (§9) close the loop to
  SP1's Rust implementation.

Every conjunct of every chip Spec was adversarially re-reviewed for this report against the Sail
clauses and SP1's Rust executor (the 2026-07 release-readiness audit, batches A1–A7; findings
log archived in git history at `14c926bd`):
operand order for the non-commutative ops, sign-extension and mask widths for all six shifts,
byte-lane selection and extension widths for all loads, and the store merge math (proven to
preserve untouched bytes) — with zero soundness findings.

### 5.2 The hard case: DivRem's evidence contract

Division is where zkVM constraint bugs classically live (underconstrained `q·b + r = a`
identities). The DivRem chip uses a dedicated contract design
(`FormalModel/Contracts/DivRem.lean`): the eight opcodes partition into **four semantic
families** (signed/unsigned × 64/32-bit), each defined by an evidence record whose Euclidean
identity is stated over **full-precision ℕ/ℤ** (not modulo 2^64) together with the exact
remainder-bound, sign, divide-by-zero, and INT_MIN/−1 overflow conditions. The audit confirmed
the families are *total* (one-hot selection is forced on real rows) and *uniquely determining*
(the conditions pin quotient and remainder — precisely the property whose absence is the classic
bug). Circuit-independent lemmas (`Proofs/Chips/DivRemChip/Cases.lean`) take evidence to the ISA
result; the one heavy arithmetic seam is the whole-chip `evidenceSoundness` theorem deriving the
evidence from circuit facts plus two disclosed operand-range assumptions.

### 5.3 What the per-chip audit surface is

A reader auditing a chip should read its `Spec` **together with its named closure lemmas** —
the `Spec` alone is deliberately not the whole per-chip surface. Three recurring patterns from
the 2026-08 adversarial review: the memory chips' `Spec`s state the lane-selection polynomials
whose *meaning* ("selected byte = byte `ea mod 8` of the pulled doubleword") is proved by the
grounding closure lemmas (e.g. `loadByte_selectedMemoryByte`, `loadHalf_selectedBytes`, the
`store*Chip_storeFacts` family in `SP1Clean/Soundness/Grounding/MemoryChips.lean`); the
selector-driven chips' (shifts, Lt, Bitwise) `Spec`s are flag-conditional, with the
"`is_real = 1` forces an active selector" link recovered from the physical constraints by
`selectorActive_of_mainConstraints`-style lemmas in their `Contracts.lean` files; and the
immediate-row `prev_value = op_c` bindings live in reader constraints consumed via each chip's
`advanceReady` discharge in `SP1Clean/Soundness/ChipContracts.lean`. All are kernel-checked and
consumed by the registered `advance` chain — the point is only that the audit surface includes
them.

## 6. Buses and machine-checked grounding

### 6.1 Channels carry what SP1 constrains — nothing more

Each of the five buses is a plain Clean `Channel` whose row-local guarantee is exactly what SP1's
receiving table enforces (`Model/Channels.lean`):

| Channel | Row guarantee | SP1 counterpart |
|---|---|---|
| State | `True` | the state bus has no row-local receiver checks |
| Program | `RowSpec` (register indices < 32, pc limb bound, boolean `op_a_0`) | the preprocessed program table |
| Memory | `isU64 ∧ ClkBound` (value limbs are u16s; access timestamp < 2^24) | the memory-access columns' range checks |
| Byte | `ByteRowSpec` (the AND/OR/XOR/U8Range/LTU/MSB table clauses + Range rows for every width `0..16`) | the preprocessed byte table and range table |

Crucially, channels do **not** assert reachability or execution semantics. A guarantee like
`ClkBound` is backed row-by-row by an actual receiver circuit in the ensemble (the byte/range
provider tables — mirroring SP1's own preprocessed `Byte` and `Range` chips, the latter being the
genuine receiver of SP1's `(Range, a, bits, 0)` lookups).

### 6.2 Execution truth is a conclusion, not an assumption

The global facts one actually wants — "the state messages describe a chained execution," "every
memory read sees the last write," "program rows come from the committed ROM" — are **theorems**
(`StateTruth`/`MemTruth`/`ProgTruth` in `Model/Semantics/Truth.lean`), derived by a timed
grounding engine (`Soundness/TimedGrounding.lean`, `RankedGrounding.lean`,
`GroundingAdapter.lean`, `ChipContracts.lean`) from:

- Clean's proved **channel-balance theorem** (the multiset of pushes equals the multiset of
  pulls);
- the provider/boundary tables' facts and the program commitment;
- the strict rank induced by the 24-bit access timestamps (`ClkBound` is what makes "earlier"
  well-founded — the `pull_lt_push` lemma); and
- one `advance` lemma per chip (its rows pull operands at the scheduled ticks and push the
  correctly-advanced state 8 ticks later; syscall events take 264 ticks, with the SP1 host
  behavior confined behind an explicit `SyscallHandler` boundary).

The payoff theorem of this layer:

```lean
-- SP1Clean/Soundness/GroundingInternal.lean
theorem supported_core_witness_grounding ... :
    ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows
```

where `SupportedCoreGrounding` packages: *exhaustive* (the ordered rows are a permutation of
exactly the witness's real decoded rows), *walk* (they chain program counters from the public
initial to the public final PC), *grounded* (each row's operands are the evolving machine state's
values at its ticks), and *clockCount* (`init_clk + 8·length = final_clk`).

The exported consumer endpoint is `supported_core_native_grounding`: from
`SupportedCoreNativeRelation` it returns the initial state and ordered rows together with
`InitialBoundaryFacts` and the complete `SupportedCoreGrounding` record. In particular callers can
directly consume the walk's `finalStateTruth` and `memoryFinalizeTruth`; they are no longer proved
internally and discarded by the only public capstone. `supported_core_native_sound` projects this
record onward to the plain-Sail relation `SupportedCoreSailRelation`.

This is the central methodological contrast with bus treatments that assume well-formedness
properties on read and verify them on write, justifying the global argument on paper (§11): here
the entire read-side meaning is downstream of the balance theorem and the timestamp discipline,
inside the kernel.

The comparison to StarkWare's S-two AIR verification (§11) is instructive precisely because their
memory model differs. Cairo memory is *read-only*, so S-two needs only functional
well-definedness of its memory maps, and it **assumes** this (`IsMemAssign`, enforced upstream by
preprocessed distinct-value columns — "we do not verify… add it as a hypothesis"). SP1's
read-write memory requires the strictly harder "every read sees the last write," which this
section derives in-kernel from channel balance plus the 24-bit timestamp rank rather than
assuming it. Conversely, S-two proves in Lean the LogUp lookup argument that underwrites its bus
(including a quantitative soundness-error bound), whereas we take multiset balance as an
interface and defer that layer (C2).

## 7. From grounded rows to Sail execution

### 7.1 Decode, walk, and the local chain

`Soundness/WitnessDecode.lean` deterministically decodes typed rows from the raw table witness;
the grounding walk orders them; and `Soundness/LocalExecution.lean` turns the ordered, grounded
rows into a genuine interpreter run: each row's `advance` lemma discharges one `SailStep`, and
the chain composes into a `trajectory`-style finite run of `try_step`. The conclusion object
(`Machine.ClosedLocalExecutionSegmentWitness`) carries the real run — this was verified for the
report by tracing the definition chain down to `(try_step 0 false).run`; the conclusion is not
bookkeeping around an abstract relation.

### 7.2 The machine model parameter

The headline capstone carries no machine-model parameter: its conclusion states the eight-tick
clock count directly. The model-scheduled corollary `supported_core_native_sound_scheduled`
quantifies over a `Machine.SP1MachineModel` (scheduling + boot packaging) restricted by
`UsesOrdinarySchedule` (ordinary instructions take the 8-tick schedule); it is the seam later
shard composition consumes. Only the schedule field is consumed by the shard-local corollary;
boot reachability is deliberately deferred to a later anchor. Two honest notes: (i) no
`SP1MachineModel` instance is currently constructed
in-repo, so the scheduled corollary is a parametric conditional — the configured-state core is witnessed
(`isInitialState_nonvacuous`, `FormalModel/Trace/Witness.lean`), and the relevant end-to-end bundles
have explicit joint witnesses. `JointNonVacuity.lean` proves `SupportedCoreNativeRelation` outright
for a boundary-only witness over a real one-instruction program.
`NativeCompletenessNonVacuity.lean` proves the complete admissible compiler source for a
zero-event canonical execution shard and invokes both native completeness capstones. Separately,
`ActiveTraceNonVacuity.lean` hand-assembles a genuinely active semantic trace record for
`JAL x0, 0`; its instruction-event count and decoded physical instruction-row count are both one,
and matching native provider occurrences balance all five buses. Completeness circuit-generates the
physical AIR rows, then derives both a native AIR witness and an official-Sail local execution. This
last test is the active-row assembly regression, not a full or verified trace generator.
`ActiveNativeCompleteness.lean` closes the concrete seam between those anchors: it proves one
official Sail self-jump, projects and compiles it to the exact JAL circuit event used by the active
trace, embeds the nonempty execution in the shared semantic relation, and checks bounded native
soundness on the active AIR witness. It does not prove the total compiler trace equals that
hand-assembled trace or discharge `NativeShardTraceTotal` for arbitrary executions.
The model's total boot-loader field (ROM+image loading for arbitrary well-formed programs) remains
follow-up work; (ii) the shard-local initial state comes from the boundary binding, not from
`model.boot`.

The new finite-input native core has a stronger, independently proved initialization result:
`Model/Core/Boot.lean` constructs a loaded, configured Sail state with zeroed registers for every
accepted `ProgramImage`. Its bytes and 64-bit memory words equal the ROM-overlaid sparse image with
zero defaults. `InitialMemoryLookup.circuit` and `InitialMemoryRead.circuit` authenticate byte and
word reads against concrete image-derived interval rows; both have proved constructors and
exportable witness programs. `InitialMemoryRead.Spec.initialSailState` connects the word contract
to that Sail state. `InitialRamProvider.circuit` and `InitialRegisterProvider.circuit` now emit
canonical zero-time Memory records whose values and addresses are bound to the requested boot
location (`FormalModel/Contracts/MemoryBoundary.lean`). The generic `OrderedInitialProvider.circuit`
composes either provider with a strictly increasing control link and constrains its key to the
canonical address plus one. Its executable row constructors discharge the internal completeness
conditions, and the combined witness programs are exportable. The shared
`Soundness/InitialMemoryBoundary.lean` theorem `locations_nodup` derives location uniqueness from
endpoint balance. `Soundness/InitialMemoryEnsemble.lean` now composes these providers with a
terminal table and a verifier fixing control endpoints to `0` and `2^48 + 1`. Its
`records_authentic` and `records_locations_nodup` theorems recover authentic, location-unique boot
records from local table specifications and actual Clean channel balance. The generic
`OrderedBoundaryEnsemble.interactions_eq` proves that the control ledger contains exactly the
physical boundary rows and fixed verifier pair; auxiliary tables must omit this private channel.
The unit-balance bridge retains Clean's characteristic/count bound. Empty and mixed inventories,
duplicate records/terminals, missing terminals, and disconnected rows have executable regressions.

The shared `OrderedMemoryProvider.circuit` now serves both initialization and finalization;
`OrderedInitialProvider.circuit` preserves the initialization interface as a specialization.
`FinalRegisterProvider.circuit` checks register encoding, and `FinalRamProvider.circuit` checks
bounded aligned guest RAM encoding. Each finalizer emits exactly one negative Memory record
without assuming a local Memory guarantee. Its `FinalSpec` records canonical location only;
value and clock bounds must be derived globally. `Soundness/FinalMemoryEnsemble.lean` fixes
its own control endpoints and derives `records_locations_nodup` through the common
`OrderedMemoryEnsemble.Inventory` argument. Both subsystems' `memory_interactions_eq` theorems
identify the decoded inventory with the actual physical Memory ledger, without an extra
record-correspondence premise. Finalizer constructors discharge their internal completeness
conditions, and both witness programs export. Tests cover malformed final inventories and
paired initial/final ledgers whose value or clock differs.

`Soundness/NativeCoreEnsemble.lean` integrates these providers into a new 59-table assembly,
replacing the legacy Program/init/final components. Its verifier constrains the initial PC to the
image's entry, the initial clock to one, and both private ordering endpoints. The shared generic
channel-closure theorem proves Byte/Program guarantees for all physical tables. From constraints
and balance alone, `NativeCoreBoundaries.initial_records_authentic` and
`initial_records_locations_nodup` prove the initial inventory's boot values and per-location
uniqueness; `initial_memory_interactions` identifies those records with the actual Memory ledger.
`public_boot` proves the public boot fields and canonical boundary limbs.
`NativeCoreFinalBoundary.final_records_canonical` and `final_records_locations_nodup` derive the
final inventory's location facts from these same raw premises, before Memory grounding.
`final_memory_interactions` preserves its complete negative ledger, including values and clocks.
This change removes the circular dependency of local finalizer facts on Memory guarantees;
it does not establish final values or timestamps, which remain grounding work.

`NativeCoreProgram.program_pull_committed` authenticates every active Program pull in the new
assembly against the checked image and official Sail decoder. It proves that the fixed ROM is the
only possible contributor with multiplicity other than zero or minus one, then uses Clean's
count-bounded balance to match the entire fetched message. This covers ECALL as well as ordinary
instructions without a Program-truth or execution-order premise.
This assembly retains the legacy Halt table's
padding behavior and has no boot-to-HALT execution theorem yet; the existing 55-table execution
theorem and its semantic boundary premise remain unchanged.

`NativeCoreMemory.memory_records_perm` proves that initial records plus all interior Memory pushes
are a permutation of final records plus all interior pulls, preserving complete values, locations,
and timestamps. The proof derives signed-unit multiplicities from physical constraints and uses
Clean's count-bounded balance; it retains active syscall, HALT, and refresh rows.
`memory_frontier_balance` turns this into the per-location equation with unique optional endpoints,
using the inventories' proved location uniqueness. `memoryInitialFrontier_liveOK` supplies the
generic timed engine's genesis invariant for any trajectory whose initial state is the configured
image state. Neither requires Memory guarantees or a semantic boundary premise.

`NativeCoreRows.executionRows_memory_balance` connects this physical ledger to the timed engine's
row vocabulary, retaining all active ordinary, HALT, and syscall occurrences, including the syscall
register write. Only actual MemoryBump refresh pairs remain outside the mixed carrier. The proof
uses raw constraints and balance; it needs neither HALT nor syscall inactivity.
`NativeCoreRowBalance.memory_refresh_free_of_chronology` removes those refreshes once an exhaustive
ordering, per-row Memory message permutations, aligned `RowOKCore` facts, and strict refresh
timestamp order are supplied. It preserves row occurrences and rewrites prior/final records only
to equal-value records at the same location and a no-later time. The message-permutation interface
leaves syscall read times intact; ordinary `AlignsWith` would wrongly require all of them at the
row start, a distinction checked by a kernel regression.

`NativeCoreTouches.ordered_aligned_rows` now derives the exhaustive State order and aligned Memory
rows from the combined AIR and checked image, preserving the exact per-location Memory equation
with actual refresh pairs. `NativeCoreOrder.executionRows_ordered` cancels StateBump rows internally;
`ordered_rows_timing` proves the 8/264-tick durations and boot clock residue. The ordering/touch proofs require the explicit no-wrap field bound `2^25 < p`. No ordering, touch
permutation, or syscall-inactivity premise is supplied by callers. `AlignedFacts` proves access
windows, per-location chains, and push-clock bounds. `NativeCoreMemoryOrder.ordered_memory_rows`
now derives both prior clock-limb bounds, final-frontier clock bounds, and strict refresh order
from that same balanced AIR, completing the aligned rows' `RowOKCore` facts. Initial records have
time zero, instruction/HALT/syscall pushes lie before the bounded public final clock, and
MemoryBump pushes have Byte-checked limbs; exact Memory balance transfers those bounds to every
consumed record. No final-table Memory guarantee is assumed.

`NativeCoreMemoryOrder.memory_refresh_free` consequently constructs an exhaustive ordered carrier
and refresh-free Memory ledger from just the checked image, raw constraints, and balance. It
preserves row occurrences and records each pull rewrite's unchanged read time, pushed record,
location, and value, with a no-later prior timestamp; final-frontier rewrites have the same
location/value and timestamp relation. The theorem retains chronology on the original aligned
rows. `NativeCoreTransport.grounding_carrier` now completes the transport: the rewritten carrier
has canonical State endpoints, full `RowOKCore`, both balance equations, and semantic alignment
back to every original event occurrence. `WindowAligned` replaces the ordinary alignment's
all-reads-at-start restriction with the location's pre-effect read window. Its step/frame transport
applies to arbitrary trajectories and preserves the syscall offsets.

`NativeCoreGrounding` derives the carrier's timeline by prefix-summing its State clock gaps, proves
the successor-index and public-final-clock equations, and derives initial State truth from the
boot verifier and checked image. `GroundingCarrier.ground_of_steps` then supplies all structural
and boundary premises to the generic engine. It retains the original event rows' semantic
step/frame facts as explicit premises. Under those premises, it proves grounded rewritten rows,
final State truth, and the original physical frontier's value currency at the public final State
time. Original refresh timestamps may be later than that time; only the rewritten records carry
the engine's final-time bound. `NativeCoreInstructionExecution` now derives every ordinary
instruction's step/frame facts through the component-local contracts for all 25 chips and the
carrier's proved successor timing. `GroundingCarrier.ground_of_system_steps` exposes the remaining
premises: HALT/syscall step/frame facts, the trajectory's ordinary `stepOnce` equation, and ROM
preservation. `NativeCoreTrajectory` and `NativeCoreHaltExecution` supply the ordinary successor
and HALT facts for the boot assembly's stateless handler wrapper. ROM protection, actual stateful
host effects, and terminal agreement remain open. The local stateful replay is described below;
no unconditional boot-to-HALT execution theorem is claimed.

The new semantic target is an arbitrary local segment. `Model/Core/Execution.lean` threads complete
Sail, host, and clock states through normally retiring instructions and concrete host calls.
`ExecutionPath.lean` proves identity, split/join, determinism, weighted clock accounting, and
equivalence with PolyFun finite reachability. `HostTerminal.lean` proves that only HALT produces an
exit flag; the path relation prohibits both ordinary and host steps afterward. `ExecutionReplay.lean`
checks host event data against the interpreter and threads the resulting host state. Its ordinary
Sail replay requires normal-retirement evidence before its success can be read as a semantic step.
`ExecutionBoot.lean` makes boot-to-HALT an endpoint specialization. These results do not close AIR
soundness/completeness: arbitrary finite boundary authentication, host AIR integration, compiler
totality, native witness composition, and complete event-tape export remain open. The semantic
regression composes ENTER and HALT at a non-boot clock and rejects changed host/RAM endpoints,
forged host events, and positive-length execution after HALT.

`Model/Core/HintQueue.lean` and `HostQueue.lean` add a persistent, byte-exact queue representation
and a compiler for every successful eight-call host execution. Allocations preserve historical
nodes; pops return the full hint and suffix; hook prepends retain reply order. The encoded current
queue determines HINT_LEN's actual return, including empty hints versus the empty-queue sentinel.
Local descending-pointer validity and a bounded root imply a complete finite decoded queue.
`HintQueueRecords.lean` supplies bounded 48-bit field identities and a fixed source-node lookup.
`HostHintLengthChip` constrains the current-head length and strict queue-clock advance, with exact
HostCall/node/state ledgers and exportable witnesses. Its bridge proves the full host transition
from explicit current-queue/node binding; successful dispatch supplies local completeness under
pointer/clock bounds. Joint component regressions reject forged returns and node metadata and
false empty claims. A separate allocation frontier now persists after pops and is preserved by
HINT_LEN. This prevents the constructor from reusing a historical identity when the head moves
backwards. `HintNodeAllocate` proves soundness/completeness for the fresh successor and tail link,
with explicit no-wrap bounds; its semantic extension preserves all old nodes. `HintQueuePrepend`
constructs ordered prefixes with exact row count, checked cursor continuity, and byte-exact
endpoint representation under a capacity bound. The internal operation exports 212 witness cells
and emits only three Byte requests. Byte authorization and node publication remain the enclosing
handler's responsibility; a regression demonstrates the ambiguity of equal-length metadata.
Installed queue history and HINT_READ word coverage are derived below. New WRITE/hook node
and word authorization, alignment with the CPU/host timeline, and mixed Memory grounding remain
open. Pointer bounds must also enter the shared resource profile. The full-AIR forged HINT_LEN return counterexample is not yet closed.

Original hint contents now have a native fixed word provider computed from source hints.
`HintQueueWords` and `HintQueueWordRecords` prove that the complete padded word cover plus the
authenticated length recovers all bytes, and that these values match the actual semantic RAM
write. Length is independently necessary because trailing zero bytes can have identical padded
word contents. The metadata-to-natural-length theorem discloses its below-`2^64` premise;
the word record's authenticated final-word marker now derives that bound from the final index.
The source provider has no incoming byte assumption, exact ledgers, and zero witness cells.
Its bounded position inventory never wraps; a permitted native-window write derives the needed
position bound. Generated allocation words share the checked fresh node's identity. Regressions
reject content changes, wrong keys, missing/forged padding, and length substitutions, while
retaining historical source words. Authorized new-word publication, complete HINT_READ AIR
coverage, and mixed-ensemble installation remain open.

The native `HintReadSpan` circuit checks a positive count of `length / 8 + 1` words and the last
written address, including writes ending exactly at `2^48`. Its constructor is complete for
aligned permitted writes in the native window, and it exports 116 witness cells with six Byte
pulls. `HintReadSpan.Spec.node_end` combines the span with authenticated metadata and the actual
final word to recover the natural node length and complete padded count. This authentication is
necessary: a length of `2^64` has the same encoded length word as zero and would otherwise pass a
one-word span. A symbolic regression proves such a node has no bounded authenticated final word;
executable regressions reject forged markers, counts, endpoints, and out-of-window padding.
The physical `HintReadWordChip` consumer now connects each immutable word pull to one actual
RAM transfer and all eight byte-permission requests, including padding. Its exact cursor advances
the word index without wrap and preserves the call clock and node identity. Both variants export
265 witness cells. `HintReadCoverage.ordered_cover` derives an exhaustive walk of the physical
consumer tables and an exact consecutive index inventory from their own unit cursor balance;
`balanced_of_walk` proves the converse under Clean's characteristic count guard. The constructor's
successor bounds follow from a checked span. Regressions retain physical row reordering and writes
at the address ceiling while rejecting missing/repeated words, wrong clocks, forged values/end
markers, and absent or read-only padding permissions.

`HostHintReadChip` now connects the full call, current queue head, checked span, and authenticated
final-word request. Its circuit has closed soundness/completeness proofs and exports 302 witness
cells. The host bridge derives the exact natural length, queue pop, and complete padded-write
request from bound records, register observations, and writable permission; successful dispatch
constructs all row assumptions under the stated store/clock bounds.
`HostHintReadCoverage.complete_indices` uses the physical handler's own cursor interactions and
the consumer tables' balance to derive the exact actual-node word inventory. Executed regressions
join the instruction handoff, handler, fixed sources, word consumers, and permission providers;
the instruction's other channels remain external. They retain reordered rows and final-cell
writes and reject omitted/repeated words, locally valid forged final contents, malformed spans,
and changed queue frontiers.

`HostHintReadWrites.run_of_tables` combines successful concrete host execution with exact physical
word-write agreement, including all padding. `HintReadWrites.ordered_writes` derives every word's
address and value from the exhaustive walk and its authenticated records. `HintReadWriteLedger`
projects the actual Memory pairs and byte-permission pulls; its `memory_readback` agrees with the
semantic byte update, and `permitted_of_inventory` derives permission for the complete padded span.
Authenticating only the handler's final word does not suffice: an executed regression swaps the
consumer markers, balances the cursor, and repeats a destination address. Authenticating every
consumer word rejects this substitution. This is a subsystem-premise regression, not a new full-AIR
counterexample. Local specifications, current-queue/node/word bindings, incoming register observations,
and permission authentication remain explicit premises.

`HostHintReadPartition.run_of_shared_tables` now derives the per-call balance internally from
the actual shared handler/consumer cursor ledger and unique handler clocks. Selecting an event
retains its original table rows, data, and all-channel interaction provenance. Its
`consumer_has_handler` theorem also excludes orphan consumers, using their strict index progress.
The generic `ToClean/Air/MessageFilter.lean` transport preserves the characteristic count guard when
restricting balance to complete message classes. Word authentication refers to the selected call's
current store, allowing later WRITE/hook allocations instead of assuming a static queue store.
Executed tests retain different nodes, lengths,
destinations, reversed physical rows, and clock carries, and reject missing handlers and consumers.
Another regression duplicates complete calls: the cursor still balances, while handler-clock
uniqueness fails. This records a required integration condition, not a new full-AIR counterexample.
`Soundness/LocalCoreEventUniqueness.lean` theorem `executionRows_clocks_nodup` now derives distinct
incoming clocks for every active ordinary, HALT, and syscall occurrence from actual local AIR
constraints and balance. It does not require a boot source or HALT endpoint.
`Soundness/HostCallLedger.lean` theorem `calls_perm` derives complete typed call permutation from
the actual wrapper handoff and unit consumer pulls. The binary gate follows from raw constraints;
padding remains in the original characteristic count bound.

`Soundness/LocalCoreEnsemble.lean` now separates `OrderingChannels`—State balance and Byte
guarantees—from full Memory balance. `Soundness/HostLocalCore.lean` installs the wrapper at the
actual syscall position in a protected 60-table prefix and appends host components. Its
`localWitness_constraints`, `localWitness_byte`, `localWitness_state`, and
`hostCallTable_projection` theorems preserve original constraints, required Byte guarantees,
the complete State ledger, and the exact active instruction inventory over unchanged physical
arrays. The full source, verifier, data, and public endpoints are retained.
Its `executionRows_ordered` and `hostCalls_clocks_nodup` theorems derive the exhaustive CPU
walk and call-clock uniqueness from this extended ensemble's own constraints and balance.
Auxiliary components must prove their Byte requirements locally and have no CPU State
interactions; these are static component properties. `Soundness/HostHintReadHandoff.lean`
theorem `auxiliaryInterface` proves them for the actual HINT_READ handler and both RAM consumer
variants.

No projected Byte or Memory balance is needed. The executed `installedMemoryProjection`
regression in `SP1CleanTest/Core/HostCall.lean` checks an installed WRITE row with padding:
original assertions/lookups and State edges survive, but a frontier that balances the wrapper's
Memory ledger fails after the x12 pair is dropped. The earlier local-witness corollaries remain
available with their original stronger hypotheses.

`Soundness/HostLocalHandoff.lean` theorem `calls_perm` now derives the complete instruction/
handler permutation from the actual registered tables and this ensemble's own balance.
`Soundness/LocalCoreChannels.lean` and `Soundness/HostLocalCoreLedger.lean` prove silence of
all retained non-wrapper tables. `ToClean/Air/ReceiverView.lean` provides the generic typed
receiver inventory and its exact physical ledger equation. Resources must be statically silent
on HostCall, so they cannot hide an omitted or extra handler. Complete messages, multiplicities,
and the original characteristic count bound are retained.

`Soundness/HostCallReceivers.lean` supplies the actual HALT, ENTER, both eight-slot commitment
families, and empty/nonempty HINT_LEN receivers. `Soundness/HostHintReadHandoff.lean` adds
HINT_READ and proves the 21-handler chronology interface and both word consumers' HostCall
silence. Its `handler_clocks_nodup_of_registered` and `balanced_for_of_registered` corollaries
remove caller-supplied handoff accounting equations. WRITE and VERIFY handlers are not yet
implemented or covered by this registry's completeness.

The `registeredReceiverHandoff` regression in `SP1CleanTest/Core/HostCall.lean` checks actual
rows from three handler kinds in the real registry, reversed instructions, and padding; missing
or duplicate receivers fail HostCall balance. This checks the handoff subsystem, not a complete
host-execution witness. Earlier tests reject forged return limbs and show that duplicating both
inventories balances handoff alone; CPU ordering excludes that case.

`Soundness/HostHintReadLocal.lean` installs the real handler and both word variants in fixed
physical positions and declares every channel used by its host components, including queue and
word channels. Its `cursor_interactions` and `cursor_balanced` theorems derive the full shared
cursor ledger from this witness's own balance; `balanced_for` also derives per-call balance and
physical alignment. Other components satisfy static cursor silence. Its `consumer_has_handler`
excludes orphan word consumers using their local specifications and strict index progress.

`Soundness/HostLocalCorePermissions.lean` proves that the retained fixed image table remains
the sole positive permission source when host auxiliaries are unit consumers. The two physical
word variants have those proved unit ledgers. `Soundness/HostHintReadLocalPermissions.lean`
theorem `word_permission_policy` combines provider-authenticated writability and the upper bound
with the checked handler span's lower native-window bound, propagated through the authenticated
consumer path. Its `run_of_witness` theorem derives concrete
HINT_READ dispatch and the exact padded word inventory without separate handoff/cursor balance,
table alignment, clock uniqueness, or per-byte permission premises. Local row specifications,
current queue/node/word bindings, and current register observations remain explicit. A `Binds`
predicate describes semantic contents and does not by itself establish canonical field encodings.

The `installedCursor` and `installedPermissions` tests in `SP1CleanTest/Core/HostHintReadPartition.lean`
use an actual 83-table ensemble witness. They check reversed multi-call rows, clock carries,
missing handlers/words, orphan consumers, the last native RAM cell, and missing permissions.
Padding into ROM can still balance the cursor; valid provider constraints and permission balance
reject it. Forged provider rows restore the permission ledger only by failing those constraints.
These are channel/subsystem regressions, not complete host-execution witnesses.

`Soundness/HostHintReadLocalRecords.lean` now authenticates every actual node and word pull,
including canonical field encodings, through the complete installed ledger. The pure Clean
rules in `ToClean/Air/Authentication.lean` distinguish component-local authentication from
authentication of actual physical table rows. Fixed sources prove the former from raw lookup
constraints; future allocation providers may need prior grounding facts to prove the latter.
The current handler registry and both word consumers cannot create node or word sources.
`source_record_authentication` closes the fixed-source registration using the complete snapshot's
hint bytes, with binding preserved under persistent store extension. `handler_spec` derives the
local handler contract. `word_steps` extracts the bundled step circuit's soundness using only
Byte and authenticated word guarantees. The coverage and permission proofs consume this weaker
contract; `word_spec` retains the Memory guarantees needed for the full RAM contract.

The `installedRecords` regression uses the actual 85-table source registration with repeated
demand and reversed rows. Missing source rows fail record balance. Changing fixed source bytes
leaves the claimed ledger balanced but fails the lookup. `noncanonicalNodeLength` exhibits a
length whose decoded 64-bit value agrees with the honest record while its field encoding is
rejected by the source lookup. These tests concern the record subsystem, not full AIR satisfaction.
Record authentication in a persistent store alone does not establish that a pointer was available
at an earlier call. `HostHintReadLocalExecution.current_records` supplies the missing restriction
from the current queue head, store extension, and actual per-call cursor path. Its
`run_of_authenticated_witness` theorem proves concrete dispatch and the complete padded write
inventory without caller-supplied local specifications or individual node/word bindings.
Current queue truth, authentication of the persistent store,
and current register observations remain explicit; prior Memory guarantees are not required.
The `futureNodeConsumers` regression substitutes
a later node with identical bytes: source checks and complete record balance still pass, but
the actual cursor ledger rejects its use by the earlier call. This is also a subsystem regression.

`Soundness/HostQueueOrder.lean` now orders all physical HINT_READ and both HINT_LEN rows by their
complete queue tokens. `HostHintReadLocalQueue.queue_interactions` retains the full installed
ledger, including every extra resource contribution. Its `queue_specs` derives the three handler
contracts without Memory premises. `queue_ordered_of_endpoints` proves the exhaustive token path
conditionally on the actual resource endpoint ledger; that interface does not construct or
authenticate endpoints.
The stronger negative result `source_queue_rows_nil` proves that the fixed node/word source
assembly, with full AIR constraints and balance, forces all three queue-handler tables inactive.
Thus its active 85-table record fixtures cannot be complete AIR witnesses. `missingQueueEndpoints`
checks their record balance succeeds while queue balance fails; adding the correct explicit endpoint
pair closes that ledger, and altering its final head breaks it again. The pair in this regression
is not an installed verifier. The new `Soundness/HostHintQueueBoundary.lean` assembly now runs the
endpoint circuit exactly once in the actual verifier. The source cursor binds to the full incoming
hints under a circuit-checked capacity bound; the final cursor is a fixed ensemble parameter.
Generic `ClosedVerifier` transport preserves raw constraints in both directions and the complete
ledger on every channel, including count bounds. It requires static offset/environment transport
laws, proved by the endpoint circuit; zero witness length alone would not imply those laws.
`source_queue_ordered` orders all actual HINT_READ and both HINT_LEN rows from the installed AIR's
constraints and balance alone. `installedQueueEndpoints` checks the real verifier closes queue
balance and its derived singleton preserves it, while duplicate chains, forged heads, and reset
frontiers fail; the zero-event identity succeeds. These remain subsystem checks. No outgoing
snapshot binding follows merely from fixing a final cursor. The new
`Soundness/HostHintQueueHistory.lean` now derives complete semantic queue replay from that same AIR.
Its `source_history` theorem records head/frontier truth at every prefix and checks each observed
length and consumed natural length. `terminal_bytes` proves the final cursor's decoded bytes equal
replay's remaining queue. `History.current` exposes current-store binding for later grounding.
The generic `HintQueueHistory.of_walk` permits persistent inventory growth; the model's
`HostState.hintEvent_sound` covers all eight successful host calls, including complete WRITE/hook
prepends. The installed instance only covers HINT_READ and the two HINT_LEN variants with other
resources queue-silent. `Soundness/HostQueueCPUOrder.lean` now derives the structural alignment
with CPU execution: every physical queue row consumes a complete call from the active instruction
wrapper, and the queue clock sequence is a subsequence of every exhaustive CPU walk.
`call_cpu_at` identifies the exact instruction at the matched clock. Its combined `source_history`
theorem derives both paths, byte replay, and `CurrentQueues` from the installed constraints and
balance. The latter recovers current bytes/frontier by replaying exactly those queue events whose
CPU events precede the selected syscall. No caller-supplied ordering or current-head premise remains
at this interface. `Soundness/HostQueueCurrent.lean` now proves that those bytes are the evolving
host's hints after successful replay of the preceding CPU prefix. The complete receiver inventory
excludes WRITE and identifies the full semantic queue-action sequence. The HINT_READ execution
theorem consumes this equality, deriving current queue and record binding internally; its remaining
semantic inputs are the preceding replay, running status, and register currency on that same
prefix trajectory. `HostLocalCoreProgram` authenticates the wrapper's ECALL operands from the
preserved Program ledger; the dispatch proof derives all three current register observations
and their position/clock internally. Dispatch and padded-write coverage require no prior Memory
guarantees, but incoming value currency still needs the complete mixed grounding proof. The companion
HINT_LEN theorem derives the actual host observation without Memory guarantees. These statements
assume replay of the preceding prefix, not success of the current call or the remaining tape.
Authenticated allocation edges, mixed Memory grounding, and outgoing snapshot binding remain open.

`Soundness/HostLocalCoreMemory.lean` reads the actual extended Memory interior and preserves the
two boundary inventories as complete physical tables. It retains the wrapper's x12 pairs and all
appended RAM accesses; its multiplicity proof permits WRITE. The installed source-backed instance,
`HostHintReadLocalMemory.source_memory_records_perm`, derives the exact source-plus-pushes /
final-plus-pulls permutation from raw AIR constraints and balance, without a caller-supplied
Memory guarantee or multiplicity condition. `word_memory_sublist` retains every consumer pair,
including padding and duplicate occurrences. These statements establish complete-record
conservation; identifying the current predecessor value still requires mixed timed grounding.
`Soundness/HostRamTouches.lean` derives canonical RAM keys, new-word and clock bounds, and a
read at the call clock followed by a write at clock plus one, using constraints and Byte
guarantees alone. `HostHintReadLocalMemory.source_word_touches` closes these facts for the actual
installed word tables; `call_word_touches` places selected accesses in their handler's window.
`HostLocalCoreMemoryBounds.memoryInterior_push_bound` derives low-clock bounds for original
instructions and refreshes using constraints, Byte guarantees, and Program balance, and checks
WRITE's extra x12 push with the original CPU clock bounds. Auxiliary pushes retain their own
local bounds. `HostHintReadLocalMemory.source_memory_push_bound` closes those premises for the
installed source assembly; `source_memory_prior_bound` transfers them through its complete
record permutation to every consumed interior record. `source_word_order` consequently proves
strict predecessor order for every physical hint write, including padding. No prior Memory
guarantee or instruction-only Memory balance is supplied.
`Soundness/HostHintReadCPUMemory.lean` groups the actual physical words by their owning CPU events:
cursor balance supplies the handler, full HostCall balance supplies its instruction, and unique
CPU clocks make the groups an exact occurrence-preserving partition. `source_memory_partition`
retains the complete raw Memory ledger of both word tables. Authenticated node/word coverage
fixes each call's padded write inventory before identifying the current host queue, proving
distinct canonical locations and the grounding engine's per-location chain condition. Grouped
touches retain their CPU-relative timing and strict predecessor order. The `cpuWordGrouping`
regression covers reversed tables, intervening ENTER calls, final padding, a clock carry, and
duplicated consumers that selection must retain. It remains a protocol fixture, not a full
mixed-AIR witness. `Soundness/HostHintReadExecutionRows.lean` adds the grouped words to the actual
CPU events while preserving State edges and fetches. `source_execution_memory_balance` proves
conservation of the complete source/final record inventories through those enlarged rows and real
refresh pairs. `HostLocalCoreRows.memoryInterior_perm` retains the wrapper's x12 accesses in the
general decomposition; their zero gate follows from the installed source registry's full-call
projection. Future WRITE installation must retain its active pair. `source_ordered_aligned_rows`
derives an exhaustive CPU walk with aligned combined touches and unchanged complete Memory
aggregates. Word ownership identifies each nonempty group with its actual syscall; authenticated
ECALL operands restrict the original footprint to registers, disjoint from those RAM words.
The existing per-location chain rule therefore applies to the enlarged rows.
`Soundness/HostHintReadMemoryOrder.lean` bounds both limbs of prior and final clocks from the
complete host Memory balance and derives strict refresh order. The unchanged private boundary
ledgers independently establish unique source/final records. `source_memory_refresh_free` uses
the existing refresh algorithm and `LocalCore.MemoryChronology`: it retains every CPU/host touch
and rewrites priors and final records only to equal-value, same-location records at no-later times.
No instruction-only Memory balance, caller chronology, or prior Memory truth is assumed.
`Soundness/HostHintReadGrounding.lean` now constructs the canonical execution carrier for this
complete footprint and connects it to the same grounding engine as the ordinary local assembly.
`GroundingCarrier.ground_of_steps` derives source State truth and the live-memory genesis from
the verifier, source constraints, and Byte guarantees. Given the complete original events'
step/frame facts on a trajectory starting at that source, it derives their register/RAM operand
values at the actual read times, final State truth, and physical final-frontier values at the
outgoing clock. The proof hides alignment and refresh rewriting. It does not infer truth at an
original prior record's historical timestamp. Complete event semantics on paired replay, complete
outgoing snapshot agreement, and integration of the remaining host effects are still open.
`Soundness/HostHintReadTrajectory.lean` now instantiates actual paired Sail/host replay on that
carrier. For a handler matched to its CPU occurrence, `GroundingCarrier.hintLength_result`
derives the actual queue-length observation from
incoming State truth. `GroundingCarrier.hintRead_run` derives concrete HINT_READ dispatch and
the exact padded-word inventory from that truth and original operand currency. Both conclusions
identify the physical CPU event at the returned prefix position. No preceding-replay or
running-host premise is supplied: the former follows from incoming State truth, and the latter
from the checked source and authenticated ECALL fetch. The shared `CoreExecutionTrajectory`
proof identifies the carrier and semantic event timelines at every index, including the
non-executing extension past the tape.
`Soundness/HostHintReadMemoryEffect.lean` now proves `GroundingCarrier.hintRead_step`: incoming
State and operand currency imply an actual full-state HINT_READ transition to the next paired
replay state, with exact values for every physical RAM push and preservation of every other RAM
cell. Complete HostCall agreement supplies the arguments/result; the instruction contract and
clock bounds supply the PC law and non-wrapping clock recombination. The physical write inventory
includes the mandatory padded word and does not require an assumption about overwritten bytes.
`GroundingCarrier.hintRead_engineFacts` supplies the complete timed step/frame bundle for a
matched physical HINT_READ, without a caller-supplied semantic effect or successful-step premise.
The x5 write is read back at offset 4; x10/x11 retain their authenticated values at offsets 3/2.
Every grouped RAM push has its bounded value at the corresponding access time. The frame proof
covers both untouched locations and written locations whose pushed value matches the invariant.
`Soundness/HostExecutionEffect.lean` derives configuration and protected-byte preservation from
the concrete host transition, including transitions that modify RAM; this supplies ROM preservation.
`GroundingCarrier.hintLength_run` and `hintLength_step` derive the complete HINT_LEN successor
for either queue variant from its actual observed length and incoming grounding invariant.
`source_wordsAt_nil_of_not_read` derives the absence of added hint RAM rows for non-read events:
every physical word has an authenticated HINT_READ owner at its unique CPU clock.
`GroundingCarrier.queue_engineFacts` combines HINT_READ and both HINT_LEN variants behind one
timed step/frame statement. `HostHintReadInstructionExecution` supplies
`GroundingCarrier.instruction_engineFacts` for all 25 ordinary instruction families on the same
complete carrier. Its static chip inputs use the preserved Byte/Program facts. Every ordinary
store's byte permission is authenticated by the extended assembly's actual ledger, and the
registered row effects preserve ROM. Hint-word ownership excludes added RAM rows at ordinary
instruction clocks. `HostQueueCallProjection.calls_run_or_queue` classifies the complete installed
call inventory; `HostHintReadSyscallExecution` derives every SyscallInstrs step/frame bundle using
that classification. HALT and ENTER use their existing dispatch bridges; COMMIT's new
`run_of_callSpec` updates the actual host bank, preserving its other slots. It makes no claim that
the row's prior bank or the complete final bank snapshot has already been authenticated.
`HostHintReadExecution` proves `HostHintReadCPU.GroundingCarrier.ground`, combining all ordinary,
syscall, and legacy HALT cases. It derives the original operand currency and final
State/Memory frontier truth without caller-supplied event semantics. The legacy HALT table retains
its 16-bit exit restriction. `Soundness/HostHintReadExecutionPath.lean` now proves
`HostHintReadCPU.source_execution`: the installed AIR's constraints and balance yield an
`ExecutionPath` from the actual complete source, with exactly the active event multiset and
agreement at final PC, clock, and every physical Memory-frontier record. Ordinary retirement is
derived from the registered chip contracts and grounded operands; successful Sail replay alone
would not suffice. Host transitions use the concrete interpreter's actual incoming state. Inactive
padding is erased and empty segments are identities. This statement does not bind a supplied
complete outgoing snapshot or the Exit bus. Those obligations, the two missing handlers, and
constructive completeness remain open; no full eight-call AIR/execution equivalence is claimed.
Registration does not by itself establish active COMMIT coverage: this source-hint assembly
does not install the commitment-bank endpoints. The separate `HostCommitEnsemble` now fixes its
incoming bank from the actual complete source host, and `sound` derives the physical bank history
from that host to the public final values. A zero-clock seed avoids claiming a historical last-call
time. Nonzero-source regressions preserve values across a bank-shard cut and reject reset sources,
untouched-slot mutations, and forged outgoing high limbs. Both bank endpoints and their terminals
still need installation and CPU-history agreement in the mixed ensemble before outgoing bank
authentication or active-COMMIT completeness can be claimed there.

`physicalQueueHistory` decodes the real handler tables in physical order, sorts their events by
clock, and replays interleaved length observations and reads, including an empty hint and an
empty queue. A stale length forged in both return and metadata keeps local assertions and queue
token balance satisfied but fails the source lookup and semantic replay. `queueReplayPrepends`
checks allocation-compatible byte replay and the empty-hint/empty-queue distinction. These tests
still do not construct a full mixed-AIR witness. The queue's positive
event-clock requirement falls under the existing active 1-mod-8 compiler profile; it does not
require rejecting zero-step identities at clock zero. `queueCPUHandoff` adds a physical-wrapper
handoff check with 264-tick syscall spacing, two intervening ENTER calls, reversed tables, padding,
and a 24-bit clock carry. It checks queue replay and rejects a changed full call despite unchanged
clocks. `queueCPUProjection` additionally checks the shared decoder's complete queue actions.
`queueHostReplay` executes two consecutive HINT_READ calls against the actual paired host/Sail
state, checking successive queues, overwritten RAM, the extra padding word, unrelated RAM/output,
and failure of a third read on the empty queue. `queueWriteNeedsAllocation` checks why erasing
WRITE would lose real prepends. These fixtures still do not establish complete State/Memory AIR balance.

The extended assembly's automatic channel list retains duplicates. Repeating a balance
requirement does not change the Lean relation, but this list fails the exporter's unique-name
requirement. Exporting this assembly still needs a canonical channel inventory with proved
coverage and name identity; no full-assembly export instance is claimed here.

Full integration must authenticate new WRITE/hook allocations and incorporate host Memory transfers into mixed grounding with
predecessor currency and complete outgoing-state agreement. The full HINT_LEN counterexample
remains open.

Arbitrary source-provider components are now installed in `LocalCore.ensemble`.
`MemorySnapshot.Realizes` compares
all integer registers and every byte below `2^48` with Sail, including locations absent from a
shard's touched inventory. `MemorySnapshot.equivalent_iff` proves that executable comparison over
the finite sparse supports is exactly this RAM/register equality. It does not compare the full
Sail/host/clock state. The snapshot register provider authenticates index and complete value through
a 32-row fixed lookup; the RAM provider authenticates the snapshot's eight bytes and canonical
aligned address. Both have sound/complete ordered wrappers, proof-independent constructors, and
exportable witness programs. Boot RAM uses this same implementation. Regressions reject forged
limbs, substituted indices, changed source bytes, unrelated ordering keys, and untouched-memory
mutations. The local 59-table assembly shares the boot assembly's instruction/finalizer/provider
suffix and binds its incoming public PC/clock to a supplied complete execution snapshot.
`LocalCoreBoundaries.lean` derives source-record authenticity, uniqueness, the exact physical Memory ledger, and canonical public fields
from raw constraints and balance, without caller-supplied provider or source-truth premises.

The local verifier's `checkExecutionSource` checks program validity, supported decoding, all Sail
registers present, the existing platform configuration, all committed ROM bytes in source RAM, and
48-bit source PC/clock bounds. Source-provider authentication alone would leave code bytes
unconstrained against the Program table when the shard never reads them as data. The executable
checker has a proved semantic contract, and `SourceFor.clock`/`SourceFor.pc` prove that the incoming
field token decodes to the actual source clock and Sail PC without aliases.
`LocalCoreSourceGrounding.initialStateTruth` and `memoryInitialFrontier_liveOK` derive the initial
State and live-memory facts from raw constraints and balance for any trajectory starting at that
source. Zero-time source records are admissible local seeds at nonzero shard clocks; they do not
claim historical last-access times. The full assembly regression runs ADD at clock 9 with nonzero
incoming registers, executes Byte/Range providers, and checks constraints, fixed lookups, channel
membership, count bounds, and full-message balance. It rejects missing registers, invalid platform
configuration, unbound source PC/clock, out-of-range sources, and changed untouched ROM.
These are source-grounding and executable AIR results. Complete outgoing Sail/host agreement,
active host effects, and stateful HALT/Exit agreement remain open. Source validity
allows a stopped host for empty segments. The verifier now freezes that source's clock, and
strict State ordering proves absence of all active rows after HALT.
No arbitrary-boundary AIR equivalence is claimed.

The local assembly's finalizer contracts, canonical locations, per-location uniqueness, and exact
negative Memory ledger now follow from raw constraints and its Byte/order balances.
`LocalCoreMemory.memory_records_perm` and `memory_frontier_balance` establish the complete-message
permutation and per-location source/final equation, retaining all interior occurrences, including
active syscalls. Component multiplicity and boundary algebra are shared with the boot proofs in
`CoreMemoryBalance`; no Memory-truth, execution-order, or syscall-inactivity premise is added.

Program authentication and State ordering are also proved for the local assembly.
`LocalCoreProgram.program_pull_committed` authenticates any active fetch against the image's
ROM/Sail decode through actual Program balance. `LocalCoreDecode` retains physical cells and
constraints. `LocalCoreRows.executionRows_memory_balance` accounts for every active ordinary,
HALT, and syscall occurrence, with actual refresh pairs separate. `LocalCoreState.state_endpointBalanced`
and `LocalCoreOrder.executionRows_ordered` derive an exhaustive canonical State walk between the
public endpoints. `ordered_rows_timing` gives each row's exact 8/264-tick duration and incoming clock
residue. No ordering or syscall-inactivity premise is accepted. Component semantics and physical
ledger algebra are shared with boot in `CoreProgramBalance`, `CoreExecutionRow`, and
`CoreTableProjection`; the existing generic decoder and `StateChronology` prove the common
algorithms. Regressions accept reversed physical instructions with padding and empty segments,
and reject unauthenticated Program fetches. Aligned touches, prior-record bounds, and refresh
elimination are now transported; the remaining execution trajectory must thread the actual host state.

`LocalCoreMemoryOrder.ordered_memory_rows` derives complete aligned row contracts and both
24-bit clock bounds on prior, refresh, and final records from the produced side of Memory balance.
`memory_refresh_free` eliminates actual refresh pairs while preserving read times and pushed
records, moving only equal-value priors/finals at the same location to earlier timestamps.
`LocalCoreTransport.grounding_carrier` then supplies the canonical State walk and both balances.
`LocalCoreGrounding.GroundingCarrier.timeline_source` binds its timeline to the complete source's
clock. `ground_of_steps` derives initial truth internally and concludes final State truth and
physical final-record value currency from original-event step/frame facts. This is an explicitly
conditional grounding theorem; stateful execution, host effects, ROM preservation, and complete
outgoing-state agreement remain to be closed.

`LocalCoreTrajectory` now fixes the paired Sail/host replay from the complete source and the
ordered event tape. Its successful prefixes have exactly the clocks of the AIR timeline.
`LocalCoreInstructionExecution.GroundingCarrier.instruction_engineFacts` derives all ordinary
step/frame facts on that replay. The running-host guard follows from the replay's terminal-PC
invariant and authenticated code fetch; the non-ECALL guard follows from official decoding.
`LocalCoreHaltExecution` additionally authenticates HALT's committed ECALL through the actual
Program ledger. Its asserted zero code and upper exit limbs, together with incoming register
currency, determine the current x5/x10/x11 and an actual stateful HALT transition. That transition
records the exit status and preserves the complete host and Sail state except for the exit field
and PC. The host policy characteristic explicitly agrees with the field. The existing HALT row's
exit domain is only 16 bits; the concrete host permits canonical 32-bit exits below the characteristic.
This remains a completeness restriction pending integration of the full syscall/Exit path.
`ground_of_host_steps` therefore needs only ROM preservation and active SyscallInstrs semantic facts.
It does not assume successful replay or an execution path. `replay_of_finalTruth` recovers successful
full-tape replay and its complete returned state with the public PC/clock. Ordinary normal retirement,
the other host effects, terminal Exit-bus agreement, and complete outgoing-state agreement remain
necessary for the execution theorem.
The trajectory holds its endpoint after the tape; regressions distinguish that mathematical
extension from appending an actual instruction, which fails after HALT.

`ProtectedLocalCore.ensemble` adds byte-level ROM write protection to the local AIR. Its four
store wrappers retain the original physical widths, assertion/lookup lists, and all existing
interaction ledgers, with proved equalities. They request permission for exactly the bytes written;
a new provider authenticates those addresses against writable intervals computed from the fixed
ROM. The table grows with ROM size, not the 48-bit address space. Its constructor is proved total
exactly for in-range writable addresses. Comparison and provider witnesses use exportable Clean
operations, with no additional Byte traffic. Full-AIR regressions reject a store that overwrites
its own instruction and forged/missing permissions, while accepting writable bytes in the other
half of the same eight-byte cell, all four store paddings, and stopped-source identities.

This is a native immutable-code profile restriction; the 25 original Rust-faithfulness anchors
are unchanged. `ProtectedLocalCoreProjection` now projects the complete physical witness to
`LocalCore`, preserving constraints, exact old ledgers, data, and public input. Its
`statement_implies_local` proves refinement at the same public boundary. The exhaustive component
classification in `ProtectedLocalCorePermissions` proves that the fixed interval provider is the
only permission source; count-bounded balance authenticates every active pull, including the
`row_pull_permitted` physical-row interface. No provider-validity premise is supplied externally.
`ProtectedStoreFootprints` identifies those requests with every byte covered by the four stores'
committed `MemWrite`; `ProtectedLocalCoreRom.instructionRows_write_permitted` transports the result
to every decoded instruction using its physical table provenance. The row-effect grounding interface
uses `RowEffect.romLoaded_of_writePermission` internally. Consequently
`ProtectedLocalCore.ground_of_host_steps` derives ordinary and HALT step/frame facts without a
ROM-preservation premise. Active SyscallInstrs step/frame effects remain explicit. Host-memory writes
must join the same permission interface when their effects are integrated. Complete outgoing-state
agreement, terminal Exit agreement, and compiler totality remain open; full local
soundness/completeness is not yet claimed.

The local verifier now constrains a stopped source to have equal incoming/final clock limbs.
`LocalCoreMemoryOrder.executionRows_nil_of_stopped` uses strict State progress to exclude every
active ordinary, HALT, and syscall row. This fixes the reproduced AIR-valid ADD-after-HALT case,
while `acceptsEmptySegments` retains stopped-source identities. Additional regressions exercise
three touches to one register and actual 24-bit State clock canonicalization. `clockPhaseNeedsProfile`
records a domain condition for completeness: clock range validation alone admits 10, whereas the
active CPU requires the SP1 1-mod-8 phase. The pure semantic execution path remains broader; the
shared native compiler profile must state that phase for nonempty segments.

The complete 59-table regression includes active HINT_LEN with nonzero source registers and a
264-tick State edge. It also runs at the maximum 24-bit high clock using one refresh per touched
register, without rows for the intervening epochs. Missing/duplicate touches and unmatched final
values or times are rejected. The regression also reproduces the unclosed host boundary: the supplied host's next hint has length 3, but
changing the instruction return and corresponding final register record together to 4 still
passes every current AIR check. `hintReturnNeedsHostBinding` records this mismatch against the
finite host interpreter. Thus these ledger results do not establish final-value currency or an
AIR-to-execution implication; stateful host-result constraints and the mixed execution walk remain
required for the capstone.

`Model/Core/ExecutionSnapshot.lean` now represents full execution boundaries with finite data.
It preserves every Sail register and missing key, runtime cycle count and output, all host fields,
and execution clock. Sparse RAM realizes exactly the bounded Sail map: bytes inside the window
are present, and outside addresses are absent. Executable comparison is proved equivalent to
literal equality of realized `ExecutionState`s. It detects changes to `nextPC` and `minstret` even
when the integer-register/RAM projection agrees. Resetting those bookkeeping fields at a shard cut
would not preserve the existing exact-state path semantics. Boot has a proved representation;
initialized full snapshots project to the source-provider representation.

`Model/Core/HostSnapshot.lean` executes host calls on the finite representation. Its commuting
theorem, soundness, and completeness match the Sail host adapter on the complete state, under the
native policy's fixed memory window. Padded HINT_READ writes are included, and all untouched fields
are preserved. The active regression computes a padded hint read and derives a semantic step via
that bridge without evaluating dense memory. Exact finite equality now supports semantic identity
and composition; it is not yet an AIR constraint or a Rust boundary serializer. Complete outgoing
snapshot authentication, ordinary-step finite compilation, and native witness composition remain open.

`Model/Core/InstructionDecode.lean` now computes the supported instruction AST from a 32-bit word;
its `decode_supported` theorem limits successful parses to the routed image or the exact ECALL
encoding. `Model/Core/ProgramTable.lean` constructs complete fixed messages, proves that projection
accepts exactly the parser's domain, and proves structural ranges and exact PC recovery in the
native address window. Its finite program checker rejects unsupported entries, including unused
ROM words, without depending on the AIR field. `DecodedProgramProvider.populate_assumptions`
discharges the fixed provider's complete-message membership and range premises; its witness program
exports. Regression checks cover all 51 supported SP1 opcode projections and malformed words/messages.
`SailDecode.instructionDecode_agrees` proves uniform agreement with official Sail for every accepted
word and configured state, with 62 symbolic integer cases and exact ECALL hidden beneath the public
statement. `DecodedProgramProvider.spec_committed` connects the provider contract directly to the
validated image's actual instruction ROM and official decoder; `constraints_committed` derives
that meaning from the physical row's raw fixed-table constraints. Neither needs a decoder
certificate, and the latter needs no provider-validity or channel-balance premise. The computed
ROM has not yet replaced the released machine's program-binding premise.

The proof investigation found a parser-domain defect: enabled Sail hint extensions claim some
base-integer no-op encodings before the ordinary decoder. In particular, `0x00200033` decodes as
`NTL.P1`, rather than ADD. The executable parser now rejects all four Zihintntl ADD aliases and the
three Zicbop ORI immediate-selector patterns, while retaining neighboring supported encodings and
other `rd = x0` cases. The finite-image checker enforces this exclusion even at unused ROM addresses.
Supporting these aliases requires semantic bridges for the hint constructors; no dependency pin or
instruction-chip faithfulness theorem changed.

These boundary results do not yet give the full native capstone. Initialization specifications
are now derived inside the new assembly; finalizer address/order facts and Memory grounding,
transport of committed Program meaning to instruction pulls, and the remaining execution/host
argument are still open. The older execution theorem retains `SemanticBoundaryBinding`.

### 7.3 What is *not* claimed at this layer

No cross-shard stitching (the relation exists — `SP1ExecutionRelation`, with full-state
continuity between consecutive execution shards, last-shard canonical-halt, and ledger
authentication fields — but its soundness theorem is intentionally not declared). No syscall
host-behavior semantics beyond `ExecutableSyscallHandler.haltOnly`, the concrete handler for the
one claimed syscall; every other syscall evaluates to `none`, i.e. outside the profile. Boot
reachability appears in exactly one place — the single-shard corollary
`supported_core_boot_to_halt_single_shard` (§8.2) — and nowhere in the shard-level statements.

A deterministic native ensemble-completeness theorem is now declared (§7.4). It covers the entire
admissible native compiler image, not yet every witness of the shared bounded ordinary semantic
language.

### 7.4 Deterministic native ensemble completeness

`nativeTrace statement execution` (`Proofs/Completeness/NativeTraceCompiler.lean`) is the one total,
proof-independent low-level map from the common witness's evaluated trace to a physical native trace. Its chronological
compiler retains each `LocatedTransition`, decoded instruction, routed dependent event, access
schedule, and outgoing frontier in one record.  The construction then:

1. partitions those events by the canonical `InstructionChipId` registry and builds all 25 tables;
2. inserts MemoryBump rows through the refresh-aware field-free access scheduler and derives
   StateBump rows from consecutive state records;
3. constructs one Memory-init/final row per touched location from the canonical history;
4. stores the statement's public `SP1PublicIO` boundary once; and
5. constructs Byte, Range, and Program providers by recounting this trace's actual evaluated Clean
   consumer interactions.

Canonical provider balance is proved directly in the field.  There is no native
`ProviderMultiplicitiesFit` or `2 * m ≤ p` premise; `NativeTraceFootprint.Fits` records only Clean's
real no-wrap condition, the length of each actual channel interaction list being below `p`.

`supported_core_native_functionalCompleteness` proves this map satisfies the unchanged
`SupportedCoreNativeRelation` on `SupportedCoreNativeAdmissibleShardRelation`. The source is:

1. `SupportedCoreShardExecutionRelation`, the common event-transcript witness whose deterministic
   evaluation is an exact official-Sail ordinary segment satisfying the shared
   `CoreProfile.WithinOrdinaryRowLimit` policy;
2. `NativeTraceReady`, named facts about that exact evaluated compiler result rather than an
   existential AIR trace; and
3. the footprint bound above.

From those hypotheses the theorem derives every constraint, all seven channel balances, public-input
equality, and `SemanticBoundaryBinding`.  The State and Memory channels use temporal hand-off
permutations; Byte/Range/Program use canonical provider closure.  The older lower-level
`supported_core_generated_trace_*` theorem remains available for an already built trace, under names
which do not suggest semantic completeness.

The remaining widening gap is explicit in `NativeTraceReady`: compiler/event validity; State
chronology, bump readiness, and instruction-row agreement; Memory address/record chronology,
physical-ledger agreement, and initial content; literal-ledger consumer polarity and demand
servability; and Program-row physical projection. Configured-state decoder stability is no longer a
residual premise: committed Program rows and supported transitions share the one
`ConfiguredDecode` definition. The actual emitted interaction footprint is a separate capacity
premise. These remaining implications are exactly `NativeShardTraceTotal`. The paired
`supported_core_native_shard_sound` and
`supported_core_native_shard_functionalCompleteness` already use the same bounded relation pair;
`supported_core_native_shard_correct_of_totality` and its language-equality corollary require only
that totality theorem. The report therefore makes no unconditional public-language-equality claim.

The full completeness source itself is jointly satisfiable:
`SP1CleanTest/Audit/NativeCompletenessNonVacuity.lean` constructs a zero-event common shard witness,
proves `anchorExecution_admissible`, and invokes the functional/existential capstone and the direct
Clean-statement theorem on its literal `nativeTrace`.

The lower generated-trace assembly bundle is satisfiable in the active case:
`SP1CleanTest/Audit/ActiveTraceNonVacuity.lean` hand-assembles one semantic trace record for
`JAL x0, 0` with the matching native Byte/Range/Program/Memory provider occurrences. Its event count
and decoded physical instruction-row count are both one, preventing regression to the boundary-only
or zero-event cases, and its four explicit ledgers have lengths 4/46/2/4 and satisfy exact integer balance plus the
count bounds. `activeTrace_yields_airWitness` invokes generated-trace assembly, which circuit-generates the
physical rows; `activeTrace_yields_sailExecution` immediately invokes native soundness on the
result, reaching the model-free plain-Sail relation. The anchor demonstrates one real row through the complete assembly path; it is not yet an
inhabitant of every residual premise of `SupportedCoreNativeAdmissibleShardRelation`.

The companion `SP1CleanTest/Audit/ActiveNativeCompleteness.lean` proves that the official Sail
`JAL x0, 0` step projects through the deterministic compiler to that exact `activeEvent`, and that
both the resulting one-step semantic execution and the circuit-built active witness inhabit their
respective bounded relations. This is a joined non-vacuity regression, not an equality proof between
`nativeTrace` and the hand-assembled `activeTrace`.

## 8. The headline theorem and the conditional exact-AIR layer

### 8.1 The native relation

```lean
-- SP1Clean/Soundness/AIR.lean
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness ∧
      SyscallTableInactive witness
```

- `SupportedCoreEnsembleRelation`: the public input matches, **all** row constraints hold over
  **all** 55 tables (+ the state-boundary verifier), and **all** channels balance — verified for
  this report quantifier-by-quantifier down into Clean's `FlatEnsemble` (∀-tables, ∀-rows;
  no existential slips).
- `SP1SemanticBoundaryRelation` (= `SemanticBoundaryBinding`): there is an initial Sail state
  bound to the committed program and the provider tables' boundary facts, regrouped for reading
  as three commitment facts (program well-formedness, `Commit.StatementFor`, the committed
  initial clock), the 3-field `ShardStartState` (public initial PC, `RomLoaded`,
  `SailConfigured`), the `SailCodeMemoryCompatible` code-memory contract, and the 4-field
  assumed core `ProviderBindingContracts` (Program/Memory-init provider content and the two
  per-location uniqueness facts). The flat 11-field `InitialBoundaryFacts` remains the
  proof-layer carrier, with `semanticBoundaryBinding_iff` the kernel-checked equivalence
  (`SP1Clean/Soundness/ProviderBindings.lean`). This is an explicit
  companion *premise* — provider tables mean what they say — not something derivable from
  balance alone.

There is one interim third conjunct, and it is a placeholder rather than a claim.
`SyscallTableInactive` (`SP1Clean/Soundness/GroundingInternal.lean`) restricts the relation to
shards whose `SyscallInstrs` table has no active row (`noActiveRows`) and whose Halt table still
carries its physical row (`haltTablePresent`). The syscall chip is proved and its table registered
at ensemble position 54, but the timed grounding engine does not yet walk a syscall row's three
register touches, and the Halt table remains the sole Exit contributor. Shards with an active
syscall row are therefore outside the certified set today; the relation names that restriction
instead of assuming it away, and both fields go when the engine's row carrier admits syscall rows
and the public-value and Exit interfaces are completed.

The `< 2^24` timestamp bound is *not* such a conjunct. The physical bound on each pulled memory timestamp — the fact
that prevents timestamp wraparound at the field characteristic, and which SP1's generic
`MemoryAccess` underflow argument needs on the high-limb comparison branch — used to be a third
companion relation (`SupportedCoreMemoryTimestampRangeRelation`), because the per-chip
aligned-carrier contract took it as a premise and therefore had to know it *before* producing the
touch lists the memory balance is assembled from. Relocating it to the per-touch antecedent of that
contract's slot conjunct broke the cycle. The capstone now derives it: every record on the produced
side of the widened per-location Memory balance carries both timestamp facts — the genesis frontier
from the init provider's `assertZero clk_high`/`assertZero clk_low`, each instruction row's pushes
from its `TouchOK` window under the verifier row's range-checked `< 2^48` shard-time ceiling, and
each MemoryBump refresh push from that chip's in-circuit range checks — so by balance every pulled
record carries them too (`pushGood`/`pullGood` in
`supportedCore_orderedRows_dynamic_of_obligations`, `SP1Clean/Soundness/GroundingInternal.lean`).

### 8.2 The theorem

```lean
theorem supported_core_native_sound :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreSailRelation (p := p))
```

Read precisely: for every statement and every witness in the native relation, **there exists** a
shard-local run witness — a genuine finite `try_step` run of the official Sail RV64 interpreter,
on the committed program, in which every step retires normally (`SailRetireChain` — the trap,
illegal-instruction, wait, and extension-failure exits are excluded), starting from a
`ShardStartState` (public initial PC, committed ROM loaded, platform configured) — together with a
well-formed Memory boundary, populated per canonically-addressed, genesis-backed committed
finalize record, whose cells agree with real location content in the initial and final Sail
states (`exists_populated_memoryBoundary` from the walk's exported value currency at the
committed final clock).

The run itself comes in one of two shapes, and **which one is decided by the AIR's own algebra**:

- an `OrdinaryRun` — the run ends at the public final PC, takes exactly `(finalClk − initClk)/8`
  instructions, and the committed `exit_code` is `0`; or
- a `HaltedRun` — the normally-retiring prefix reaches a genuine `SP1Halted` state (the PC at a
  committed `ECALL` word of the guest ROM, `t0` holding the canonical `SyscallCode::HALT`, `a0`
  holding the committed exit code), and the public endpoint is that state parked at SP1's terminal
  `haltPc` one 264-tick syscall window later.

Under `SyscallTableInactive`, the Exit channel has two contributing components:
the state-boundary verifier pulls `⟨exit_code⟩` **ungated**, and each row of the Halt table (the
native replacement for SP1's `HALT` ECALL arm, ensemble position 53) pushes either its reduced
`a0` word or, when padding, the zero code. Balance alone then forces exactly one physical Halt row
and pins the committed exit code to `0` or to `reduce(a0)` accordingly, which is the case split
`supported_core_witness_grounding` performs. Two facts are disclosed with it: the Halt chip carries no
`ChipFaithful` anchor — its Rust oracle is extracted like every other
(`Extracted/SystemOracle/SyscallInstrs.lean`), but whole-row assertion and interaction equality is
false between a single arm and the multi-arm dispatcher SP1 actually compiles, which also sends on
a global syscall bus absent from the Halt circuit — and the halt row pins `a0`'s upper
three limbs to zero — a 16-bit exit-code profile restriction that is ours rather than upstream's.
SP1's halt arm bounds `op_b` to a valid field element (upper limbs zero, limb 1 compared against
`32512 = 0x7F00`), capping `reduce(op_b)` at exactly `p - 1`, so its single committed cell never
wraps; our narrower pin exists only because `HaltChip` omits that compare.

One corollary steps outside the shard: `supported_core_boot_to_halt_single_shard`
(`SP1Clean/Soundness/BootHalt.lean`) adds a *boot* semantic boundary (`BootBoundaryFacts`:
`IsInitialState` at the committed entry PC, SP1's zeroed integer register file, boot clock `1`)
and a live Halt row, and concludes a whole-program fact — from the entry point with zeroed
registers, `steps` normally-retiring interpreter steps reach an `SP1Halted` state carrying the
committed exit code, with committed terminal PC `haltPc` and committed final clock
`1 + 8·steps + 264`. It is single-shard, and it has no *constructed* inhabitant yet: the
deterministic completeness compiler still emits only the padding Halt row.

There is no
machine-model parameter and no schedule hypothesis; the model-scheduled form is the corollary
`supported_core_native_sound_scheduled` via the no-strength-lost adapter
`supportedCoreLocalExecution_of_sailRelation`. Axiom census: `propext`, `Classical.choice`,
`Quot.sound`, plus the disclosed Sail
platform hooks and `bv_decide` constants inherited from the bridges (§3.3). No `sorryAx`
anywhere in the released set (empty allowlist, gated in CI).

This existential, public-endpoint-anchored shape matches the independently developed S-two
AIR-soundness theorem (§11; arXiv 2606.04311, App. A: `∃ mem, ∃ exec, exec 0 = initialState ∧
exec (Fin.last n) = finalState ∧ ∀ i, NextState mem …`), which likewise concludes the
*existence* of a semantic execution segment between agreed endpoints rather than a functional or
verifier-level statement — corroborating that this is the natural target for an AIR-soundness
result, with the shard-local restriction being ours alone.

### 8.3 The exact-upstream layer is honestly conditional

The relation over SP1's *exact* extracted tables is
`CoreAIR.Current.ShardRelation`, whose one witness pairs the 34-table execution cluster with the
six-table Memory-boundary cluster. `GlobalValid` demands well-formed public values and exact
natural-number send/receive balance in the shared `NaturalBusLedger` representation. The relation
and its row universe are defined in `Faithful/CoreAIR.lean` +
`FormalModel/CoreAIRRelation.lean`; refinement into the common SP1/Sail shard relation exists only
through the conditional declaration below.

The native chip/grounding theorems are field-generic under their stated prime bounds. The full exact
system/public-value artifacts are not automatically so: `Global` and `SyscallInstrs`, and the
curve-seed portion of `PublicValues`, contain constants canonically encoded for SP1's KoalaBear
field. A closed exact-v6.4.0 capstone must therefore be stated at KoalaBear, or be preceded by an
explicit theorem justifying how those literals are interpreted at another prime. No generic-`p`
exact-system soundness claim is made here.

```lean
-- SP1Clean/Soundness/CoreAIR.lean
theorem sp1_air_sound_of_obligations ...
    (external : CoreAIRExternalContext binds handler programBinding)
    (proofs : CoreAIRRefinementObligations binds handler programBinding external) :
    WitnessRelation.Sound (CoreAIR.Current.ShardRelation binds)
      (SP1CoreShardSemanticRelation .base handler programBinding)
```

The total proof-free decoder and six program/loader/platform facts that are not AIR consequences live
in `CoreAIRExternalContext`. Conditional `CoreAIRRefinementObligations` has twelve AIR-facing fields:
public-value and first-shard laws; syscall transcript, operand, flag, and commit-transition laws;
Memory-boundary well-formedness and endpoint agreement; and the boundary/execution shard cases. The
substantive `executionCase` must ground the exact system-table rows as an eventful Sail segment. Every
field is consumed by the combinator. Until a closed construction exists, the unqualified names stay
reserved; conditional results remain visibly named as conditional.

The exact/native construction beneath that still-open semantic refinement is now explicit at its
local boundary. `Composition/CoreEnsemble.lean` consumes valid exact execution and
memory-boundary witnesses, a caller-supplied `CanonicalPreprocessedInventory`, and named
preprocessing, memory-boundary, and public-limb contracts, constructs exactly the native 55 tables
and verifier row, and proves every local constraint.
The Byte/Range/Program provider counts are reconstructed from the actual Clean interaction ledger of
the verifier, 25 transported instruction tables, MemoryInit/MemoryFinalize, and both bumps rather
than imported from the full exact-cluster multiplicities: the latter also count system/public
consumers absent from the native artifact. The raw exact Byte/Range/Program assertion lists are
empty. `CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening premise, to be
discharged by ArkLib; it proves neither row-local meaning nor provider selection.
`PreprocessedProviderContract` is the explicit caller premise for row-local semantics. Source
main multiplicities are not reused, and raw projected-key `Nodup` is not assumed. The
caller-supplied inventory contains matching-block source-backed carriers and separately asserts
`Nodup` for their projected keys. It may omit raw keys with zero native demand. The recount contract
then requires nonzero Byte/Program-key coverage, nonpositive skeleton sums at selected keys, and
`2 * count ≤ p`. `freshRowsByKey` is only a declarative/small-regression canonicalizer, not the
construction path. PCS/program identity, State/Memory balance, and the semantic boundary remain
separate and explicit.
The exact/native table access-permutation lemmas remain reusable transport ingredients. The unused
full-exact-payload→reduced-native-key balance closure was retired; the native provider recount and
explicit State/Memory balance contract are the live integration boundary.
`CoreArtifact.lean` names the remaining endpoint as the caller-supplied
provider-recount contract plus `ExactNativeGlobalContract`. The recount derives Byte (including
Range) and Program integer balance; the global contract retains all-channel interaction-count bounds,
State/Memory integer balance, and `SemanticBoundaryBinding`. From them the artifact derives Clean's
`BalancedChannels`, assembles `SupportedCoreNativeRelation`, and applies
`supported_core_native_sound`. No theorem currently proves joint inhabitance of that contract with
valid exact clusters. This is a useful ArkLib-facing artifact contract, not a claim that the exact
AIR already discharges it: the public Range13-quotient→native Range16 redistribution and raw
`Global`→typed-Memory lowering/cancellation remain explicit proof obligations.

## 9. Conformance testing against the real prover

Kernel-checked theorems establish soundness; they cannot establish that the formalized constraint
system is the one the *shipping prover* satisfies, nor that witness generation is live. A
dump-anchored conformance pipeline closes that gap empirically at SP1's own field (KoalaBear,
`p = 2130706433`), for **all 25 instruction chips**:

- **Committed SP1 trace dumps** (`export/sp1dump/`, 25 files): deterministic per-chip executor
  event batteries plus the **full padded `MachineAir::generate_trace` matrix**, produced by
  `chip_traces` — an ordinary committed binary at the pinned extraction branch — and
  byte-reproducible at the pin (`scripts/update_sp1_dumps.sh --check`; the recorded `sp1Commit`
  is cross-checked against the extraction pin by `scripts/check_pins.sh`).
- **The generation-time gate** (`scripts/witgenExport.lean --testdata`, re-run in CI): for every
  dumped event row, the native inputs are recovered from the dumped row itself through the
  audited symbolic row map, the chip's *own* witness programs are executed
  (`FlatOperation.witgen` over the exported shared operations), the symbolic row map is evaluated
  at the resulting cells, and the reconstructed row must equal SP1's dumped row
  **cell-for-cell** — the exporter fails closed on any mismatch and writes nothing. The
  derived padding rows (ShiftLeft/ShiftRight/DivRem) are gated the same way; a value-level
  `circuitTraceRowMapped` spot check pins the symbolic path to the audited `ChipFaithful`
  `reconfigure` map at field values on every chip. Selector-driven chips take per-event hints
  derived from the dumped executor opcode (Branch's taken-bit from the dumped operands, mirroring
  SP1's own populate) — inputs to the run, structurally incapable of laundering expected outputs
  into agreement.
- **An independent Rust reference interpreter** (`rust/witgen-interp`, ~857 fixture rows) re-runs
  the same witness programs from the wire format alone, reconstructs every anchored full SP1 row,
  and additionally checks **every extracted AIR constraint evaluates to zero** on it.

The remaining `native_decide` uses live in the separate test library (`SP1CleanTest/`, never
imported by the main library — a CI guard forbids `native_decide` there): the exportability
battery and the satisfiability anchors below, each disclosed per-declaration in the test-scope
axiom census (surfaced as generated `._native.native_decide.ax_*` constants, the v4.32.2 form of
the former named `Lean.ofReduceBool`/`Lean.trustCompiler` axioms). What conformance establishes:
populate fidelity and non-vacuity evidence on real prover data. What it does not: proof. The two
layers are complementary by construction.

Additionally, the satisfiability layer closes the vacuity questions at three levels — per-chip
rows, per-family decode facts, and the joint hypothesis bundle:

- `SP1CleanTest/NonVacuity.lean` witnesses the satisfiability of every non-trivial chip
  `Assumptions` (all 20 chips whose assumptions are not literally `True`) — mostly at padding
  rows, so it rules out contradictory *preconditions* only.
- `SP1CleanTest/NonVacuityReal.lean` goes further: for **every one of the 25 instruction
  chips**, a named, census-visible theorem exhibits a concrete `is_real = 1` row with
  non-degenerate operands satisfying the chip's **complete flattened constraint system**
  (every subcircuit `assertZero`, evaluated at SP1's KoalaBear field with the witness values
  produced by the chip's own `main` witness closures), with Lt/Bitwise/UType exercising both
  variants or outcomes and a guard theorem that every checked assertion system is nonempty.
  Channel interactions are outside any single-row statement (they are globally
  balance-checked); the rows follow the dumped Rust traces' clock discipline. This closes the
  "could a chip's constraint system be unsatisfiable on the rows that matter?" question — the
  failure mode where a soundness theorem is true only vacuously.
- The **per-family decode witnesses** (main library, axiom-clean at the default budgets):
  `Model/SailDecode.lean` reduces the real generated `ext_decode` on one concrete word per
  `instrToProgramRow` family — all 18 families — and `Soundness/Decode.lean` composes each into
  an end-to-end `decodedInROM` example on a concrete one-instruction program. A mis-transcribed
  projection arm now fails a named theorem instead of making the capstone silently vacuous for
  its rows. Restoring this evidence surfaced a live instance of exactly that hazard: the
  decoder's MUL/DIV arms test `misa.M`, which `SailConfigured` did not pin, so `decodedInROM`
  was unsatisfiable for all 13 M-extension opcodes until the `misa_m` field was added
  (2026-08-20). The per-family hoist lemmas (`decodedInROM_<family>_hoist`, all 18) additionally
  prove the strengthened ∃-instruction form derivable from the weak ∀-state one.
- The **joint anchor** (`SP1CleanTest/Audit/JointNonVacuity.lean`): a fully proved witness of
  the entire `SupportedCoreNativeRelation` at SP1's prime — a one-`JAL` statement with equal
  boundary endpoints, the 55-table witness with zero-row chip/provider tables, canonical
  committed prover data, and every `InitialBoundaryFacts` field discharged, including a real
  (non-vacuous) `SailCodeMemoryCompatible` proof via the jal step machinery. The capstone
  applied to it yields the zero-step execution; a satisfying *non-empty* shard witness is the
  trace-generator work and is deliberately out of this anchor's scope.
- The **generated twin** (`SP1CleanTest/Audit/TraceNonVacuity.lean`): the same boundary-only
  shard, but assembled through the completeness layer's builders rather than written by hand,
  witnessing `SupportedCoreGeneratedTraceRelation` — so the lower generated-trace assembly theorem
  used in §7.4 is not vacuously true of an unsatisfiable relation.
- The **active assembly anchor** (`SP1CleanTest/Audit/ActiveTraceNonVacuity.lean`): a hand-assembled
  semantic trace record for JAL-x0 whose instruction-event count and decoded physical instruction-row
  count are both one, with matching native provider occurrences and all five buses balanced. The
  generated-trace assembly circuit-generates its physical AIR rows, then passes the witness through
  `supported_core_native_sound` to the plain-Sail relation. It is not a full or
  verified trace generator.
- The **active compiler join** (`SP1CleanTest/Audit/ActiveNativeCompleteness.lean`): one official
  Sail self-jump is a valid supported semantic execution, its proof-independent projection compiles
  to the exact JAL event above, and the active circuit-built witness lies in the bounded native
  relation. The theorem deliberately stops short of identifying the complete compiler-produced
  trace with the hand-assembled one.

## 10. Trust base

Everything the results depend on beyond the Lean kernel, numbered for reference. **T** = tooling,
**M** = model premises (semantic hypotheses of the proved theorems), **C** = cryptographic layers
(future work, no claim made here). The per-theorem axiom census (`docs/snapshots/axiom-ledger.md`)
discloses which of these each headline declaration actually touches.

**What "axiom-clean" means here.** The phrase is used throughout this repository to mean the three
standard Lean axioms — `propext`, `Classical.choice`, `Quot.sound` — and nothing project-specific.
It does **not** mean a declaration's `#print axioms` output is three names long. Any theorem whose
statement reaches the Sail model also carries that model's platform hooks (T2), and a few carry
`bv_decide`'s generated constants; the capstone's census entry lists around a hundred names for
that reason. The useful split is by kind rather than by count: the Sail externs are *data-valued*
opaque operations — a proof may not assume anything about what they return, so they weaken the
model, not the logic — whereas a *Prop-valued* project axiom would be an unproved assumption and
there are none. Chip-level and AIR-level theorems that do not mention Sail are genuinely on the
three (for instance the transport layer's `transportTable_constraints` and the balance bridge's
`signedSum_eq_zero`).

- **T1 — The constraint exporter.** SP1's constraint compiler, run at the pin-checked overlay, is
  trusted to print the constraint/interaction lists its `air.eval` recorded. Mitigations: §4.1's
  fail-closed fencing, §4.3's manual re-derivation, and the independent conformance layer. The
  opcode-alphabet leg of this trust is now machine-checked rather than hand-verified: the
  extracted `Opcode` discriminant table (§4.1) is compared against the hand-maintained
  `Model/Opcode.lean` mirror by `opcodeTable_matchesExtracted`
  (`SP1Clean/FormalModel/OpcodeTable.lean`), leaving only the text-level parse of `opcode.rs`
  inside the T1 boundary.
  (Note: the exporter tooling lives on sp1's pinned `dtumad/lean-extraction` branch, not
  upstream `main`; landing that series upstream is the standing follow-up.)
- **T2 — The Sail platform hooks.** The generated model's external operations (§3.3) — opaque,
  property-free axioms.
- **T3 — `native_decide` in the test library only.** The conformance anchors trust the Lean
  compiler; the main library is `native_decide`-free (CI-gated).
- **T4 — The generated Sail model's provenance.** `Lean_RV64D` is pinned to a snapshot on
  `succinctlabs/sail-riscv-lean` regenerated from a pinned Sail compiler + pinned
  `riscv/sail-riscv` sources with the checked-in SP1 config of §3.2
  (`scripts/sail-config/generate_lean_rv64d.sh`; a stock-config run reproduces the opencompl
  base byte-identically). The trust item is the generation pipeline — the Sail compiler's Lean
  backend and the config — no longer a hand-maintained delta; the four top-level configured
  values remain disclosed as `rfl` lemmas (the two `ValidateConfig`-internal sites are visible
  in the generated source, §3.2), and every dependency stays an immutable git pin.
- **T5 — The Clean DSL is pinned to a fork.** Every circuit here is built on Clean, and that
  dependency is currently `dtumad/clean` (branch `sp1-integration`), not upstream
  `Verified-zkEVM/clean`. The base is the previous upstream pin; the delta is two upstream-destined
  branches, both with open PRs, and the pin returns to upstream as they merge. (1) `AgreesBelow`:
  `ProverEnvironment.AgreesBelow` is strengthened to constrain a prover environment's committed
  `data` and `hint`, not only its witness cells. The change is a bug fix — the example file's
  `not_computable_from_cells_alone` proves the prior obligation was *false* for any witness
  generator reading committed data — and it cannot be shimmed downstream, since Clean's own
  honest-witness-generation theorem refers to Clean's definition. `AgreesBelow` occurs in
  hypothesis position everywhere but one discharge site, so no Clean conclusion is weakened and the
  two theorems concluding with it become strictly stronger. (2) `witgen-share`: the proven
  subterm-sharing pass for witness programs (`WitgenIR.share` + the kernel-checked `eval_share`),
  which the committed witness-export goldens depend on. Full disclosure, including the standing
  rule for what may live in the fork versus this project's additive `ToClean/` library, is in
  `docs/agents/clean-upstream.md`; the pin table is in `docs/release-audit.md`.
- **M1 — The semantic boundary binding.** Provider/boundary tables mean the selected program and
  initial state (`SP1SemanticBoundaryRelation`, §8.1). Its provider-content facts are to be
  derived from the exact upstream system tables (the `executionCase` obligation). Separately, the
  exact/PCS integration must construct the demand-oriented `CanonicalPreprocessedInventory`; raw
  preprocessing does not itself supply projected-key uniqueness, coverage, or committed-program
  identity. The bundle
  also carries program/platform contracts (`SailConfigured`, `SailCodeMemoryCompatible`,
  program well-formedness) that remain application-level premises, like C-class items — no
  system-table derivation discharges them. A future unqualified exact-AIR theorem must keep those
  contracts visible as named parameters or a source-relation restriction; packaging their proofs
  inside `CoreAIRRefinementObligations` does not make them AIR consequences.
- **M2 — The memory-timestamp range bound — DISCHARGED, no longer a premise.** Pulled high
  timestamps < 2^24 (prevents wrap at the characteristic) is now derived inside the capstone from
  the per-location Memory balance rather than assumed as a companion relation (§8.1). It is listed
  here only so readers of earlier versions of this report can see where it went.
- **M3 — The syscall handler.** SP1 host-syscall behavior is confined behind the
  `SyscallHandler` interface; its faithfulness to SP1's host is out of scope.
- **M4 — The machine model.** The headline capstone is model-free; its scheduled corollary is
  parametric over `SP1MachineModel` + `UsesOrdinarySchedule`, and no instance is constructed
  in-repo yet (§7.2).
- **C1 — Preprocessed commitment binding** (`PreprocessedBinding`) — to be discharged at the
  PCS/ArkLib layer.
- **C2 — Exact natural balance.** The exact-AIR relation's `Balance.Valid` is a natural-number
  multiset equality; connecting it to the field-level LogUp/GKR argument (with its soundness
  error) is the cryptographic layer's job.
- **C3 — Shard-ledger cryptography.** Cross-shard cumulative sums and deferred-proof digests —
  the recursion/verifier layer.

Baseline logical axioms: `propext`, `Classical.choice`, `Quot.sound`; plus `bv_decide`'s checker
constants on named shift, multiply, store, jump, and byte-gadget lemmas (23 of them reach the
headline theorem, §3.3). Zero `sorryAx`; zero project `axiom` declarations; both gated by CI with
empty allowlists.

## 11. Scope comparison: the Nethermind OpenVM verification

The closest related effort is Nethermind's formal verification of the OpenVM RV32IM zkVM
(technical report, Feb 2026; Lean 4.26). It is substantial work — 45 RV32IM opcodes verified
against the Lean RISC-V specification, with an execution/memory-consistency development — and the
comparison below is about *methodological shape*, not quality. Where their scope is broader
(e.g. full RV32IM including AUIPC-class and all immediate-variant opcodes verified individually,
against a spec instantiated for RV32), we say so. **Dating note:** this comparison is against
their v1.5.0 report (OpenVM engagement commit `645460f`); the live `openvm-fv` repository has
since re-targeted OpenVM v2.0.0 with the same 45-opcode Lean surface, and additionally carries
per-chip soundness proofs for the Keccak-f[1600], Keccak sponge, and SHA-256/512 precompile chips
(against FIPS reference models) plus a three-gate axiom-footprint CI whose independent
`lean4export` re-export is a genuinely strong axiom-discipline mechanism — both real strengths
beyond the report compared here.

| Dimension | Nethermind / OpenVM | This work / SP1 |
|---|---|---|
| Target | OpenVM, RV32IM, 45 opcodes | SP1 v6.4.0 Core, RV64IM slice, 25 chips (~50 opcodes incl. W-variants and x0 paths) |
| ISA reference | Lean RISC-V spec (RV32 instantiation), per-opcode `execute_*` clauses | Same Sail lineage, RV64 generated model, full-interpreter `try_step` step relation |
| Circuit side | Transpiled/extracted constraints are the proof object; AIR columns hand-transcribed with "eyeball correspondence" macros | Independent hand-built Clean circuits; extracted lists are a *comparison target*; whole-chip bidirectional `ChipFaithful` + interaction-multiset permutation |
| Bus semantics | `BusEntry` classes: well-formedness assumed on read / asserted on write; bus *axioms* (pc bounds, timestamp bounds) justified **on paper** (their §E1–E12, §M1–M6) | Channel guarantees are row-local facts backed by receiver circuits; read-side meaning derived in-kernel from Clean's balance theorem + timestamp rank plus the named boundary premise of §8.1 (§6); zero paper bus axioms |
| Consistency | Rising-bus theorem: execution/memory bus entries can be reordered chronologically, conditional on balance hypotheses; per-opcode row-local equivalence theorems | One glued theorem: balanced constrained witness + the disclosed boundary premise (§8.1) → existence of a Sail interpreter run with matching public endpoints (§8.2); the pulled-timestamp range fact is derived from the memory balance, not assumed; per-chip statements are internal lemmas of it |
| Prover conformance | none against the real prover/witness generator (their CI gates — an axiom-hygiene scan, an in-build `collectAxioms` audit, and an independent re-export comparator — police the *axiom footprint*, not prover-trace conformance) | dump-anchored cell-for-cell reconstruction of all 25 chips' traces vs the real prover at SP1's field, plus a Rust interpreter differential (§9) |
| Crypto trust | Lookup argument + proof system assumed (their I1 = lookup/bus argument, I2 = proof system; their I3/I4 cover spec faithfulness and Lean's kernel) | Same boundary, expressed as named relations/obligations (C1–C3) with an ArkLib-shaped target signature |
| Claim discipline | Per-opcode theorems + consistency lemmas | Reserved-name policy: headline names undeclared until unconditional (§8.3) |
| Their broader coverage | Immediate-variant opcodes verified as first-class; RV32 spec assumptions (S1–S4, A1–A4) documented per-proof | Immediate variants fold into base chips (as SP1 itself does); the generator-relative completeness contracts now admit Bitwise/Lt/Addw/ShiftLeft/ShiftRight immediate forms and UType/JAL x0 rows, while semantic Sail→trace completeness remains open (disclosed, §12) |

**A third reference point: StarkWare's S-two AIR verification.** The other closely comparable
effort is StarkWare/CMU's Lean 4 verification of the S-two Cairo-AIR (Avigad, Ganor, Goldberg,
Levit, Nir, Seginer, Titelman, arXiv 2606.04311, June 2026). Its top theorem `trace_sound` has
the *same existential, endpoint-anchored shape* as ours — AIR satisfiability yields
`∃ mem, ∃ exec : Fin (n+1) → RegisterState Felt252` chaining the public initial state to the
public final state under the Cairo `NextState` relation — a useful independent confirmation that
"AIR witness ⇒ existence of a semantic execution segment between public endpoints" is the right
claim shape for a zkVM AIR-soundness result. Three axes distinguish the projects:

| Axis | StarkWare / S-two | This work / SP1 |
|---|---|---|
| AIR into Lean | Hand-re-modeled constraint-*generating* code; a fixed, collapsed component set (an idealization); trust that "the S-two code has been modeled in Lean correctly" | Pin-checked extraction of the exact shipping constraint/interaction lists, reconciled by bidirectional `ChipFaithful` |
| Semantics authority | Self-defined Cairo `NextState`, formalizing the informal Cairo whitepaper | Official RISC-V Sail interpreter (`try_step`), mechanically translated |
| Lookup argument | The LogUp lookup argument is **proved in Lean**, with a quantitative bad-set soundness-error bound | Field-level LogUp/GKR soundness **deferred** (C2); we prove only *from* multiset balance |

On the first two axes our exact-extraction and official-Sail choices are more faithful to the
shipping system; on the third, S-two reaches one layer deeper into the proof system than we
currently do, and their AIR-soundness reduction is a completed whole-program proof (theirs found
and fixed real production bugs — a missing range check and insufficient LogUp security bits)
where ours is shard-local with the `executionCase` obligation still open.

The essential difference is where the bus argument lives. Both projects face the same global
question — *why do reads see the right values?* Nethermind answers it with a well-structured
paper argument justifying bus axioms their per-opcode proofs consume. This project's answer is a
Lean derivation: the only bus facts any proof consumes are row-local guarantees enforced by an
in-ensemble receiver, and everything global is either a theorem downstream of channel balance
or a **named premise of the capstone relation** (the §8.1 boundary/uniqueness facts, M1) — never
a paper argument living outside the statement. The cost of that choice is the large grounding
layer of §6–7; the benefit is that the paper step — the usual home of subtle gaps — is either
inside the kernel or visible in the theorem's own hypotheses.

### 11.1 Findings of the public review of the predecessor effort, and their status here

The direct predecessor of this work — the 2025 chip-level verification of SP1's AIR in the same
repository lineage — was publicly reviewed by the Ethereum Foundation's zkEVM team in May 2026.
That review's findings are the natural checklist for this rebuild. Each finding is listed with
the mechanism in this tree that addresses it; every citation below is machine-checked by
`scripts/check_report_citations.sh`.

| Predecessor finding (May 2026 review) | Status in this tree |
|---|---|
| JALR's theorem assumed `(rs1+imm) % 4 = 0`, omitting the architectural `& ~1` LSB clear | The mask is a *proven Spec conjunct*: `toBitVec64 nextPcWord = ~~~1#64 &&& toBitVec64 value` (`SP1Clean/FormalModel/Contracts/Chips.lean`, the Jalr `Spec`), derived from the constraint system in `JalrChip.soundness` and consumed against the generated `execute_JALR` (which jumps to `BitVec.update target 0 0#1`) by `jalr_chip_reaches_sail` (`SP1Clean/Proofs/Chips/JalrChip/Bridge.lean`). The unconditional limb-to-word lift is `Word.toBitVec64_toNat_mod_four` (`SP1Clean/Math/Word.lean`); alignment implies trap-free retirement via `jump_to_of_mod4_eq_zero` (`SP1Clean/Model/SailWrap.lean`). |
| LH/LHU/LW/LWU theorems proved the wrong (byte-width) specification; several loads unproved or `sorry`-dependent | All five load chips carry closed per-width soundness, completeness, Sail bridges, and whole-chip faithfulness. Width and lane selection are kernel-checked: e.g. `loadHalf_selectedBytes` binds *both* little-endian bytes at `ea`/`ea+1` against the width-2 Sail read, and `loadByte_selectedMemoryByte` closes all eight lane cases (`SP1Clean/Soundness/Grounding/MemoryChips.lean`); sign/zero-extension per variant is constraint-forced (§5.3). Zero `sorry` anywhere is CI-gated. |
| SLTI's theorem was vacuously true (contradictory hypotheses) | Selector flags are circuit-constrained one-hot (never assumptions); `LtChip.Assumptions` is two operand-range facts only. Beyond structure, `SP1CleanTest/NonVacuityReal.lean` exhibits concrete satisfying `is_real = 1` rows for **every** chip's complete flattened constraint system — for Lt, both a true and a false comparison — as named, census-visible theorems (§9). |
| LUI and AUIPC had no theorem at all | `UTypeChip` has the full stack: `soundness`/`completeness`/`circuit` (axiom-clean), the bridge family through the registered `advance` (`SP1Clean/Proofs/Chips/UTypeChip/Bridge.lean`), and whole-chip Rust faithfulness `uTypeChip_faithful` (`SP1Clean/Faithful/UTypeChip.lean`) — including RV64 LUI's *sign*-extension and AUIPC's full-width carry. |
| Four project axioms, including "memory protection disabled" assumed as an axiom | Zero project `axiom` declarations in the main library (CI-gated); zero `sorryAx` across the mechanically checked released-declaration census. The sole current count lives in `docs/snapshots/axiom-ledger.md`. Platform shaping is not assumed per-proof: the Sail model is *generated* with SP1's platform configuration (§3.2), and the supervisor-only scope is a stated structural restriction (§12.6), not an axiom. |
| Version pinning and reproducible extraction were absent | Every dependency is an immutable git pin cross-checked by `scripts/check_pins.sh`; extraction is a pin-gated, fail-closed pipeline (§4.1) with byte-idempotency; the audit harness (§13) regenerates the census and fails on drift. |
| Recommendation: independent adversarial review before public claims | The 2026-07 and 2026-08 release-readiness campaigns (this report's §12 discloses their durable findings) ran blind-derivation adversarial reviews of all 25 chip Specs against the generated Sail model, per-claim validation against upstream sources, and a full file-by-file documentation sweep. |

The review also found the predecessor's public claim of 62 verified opcodes overstated (~51
complete at the time). This tree's coverage accounting is machine-checked instead of narrated:
50 covered opcodes / 3 uncovered (ECALL/EBREAK/UNIMP, routed to system tables) partitioned by
`decide` in `SP1Clean/Soundness/Coverage.lean`, with the 25-chip ↔ opcode routing mirroring
SP1's own dispatch (immediate variants fold into base chips exactly as SP1's transpiler folds
them; the mapping is the `supportedChips` table in `SP1Clean/Soundness/SupportedMachine.lean`).

## 12. Limitations, open obligations, and the path forward

Stated plainly:

1. **Shard-local, existential conclusion.** One shard segment; boot reachability and cross-shard
   stitching are specified but unproven (§7.3). No machine-model instance is constructed yet.
2. **One semantic premise** (M1): its provider-content facts await derivation
   from the exact upstream system tables — the `CoreAIRRefinementObligations.executionCase`
   closure, the substantive open mathematical obligation of the AIR layer (the bundle's
   remaining fields are smaller but equally undischarged, §8.3). M1 additionally carries
   program/platform contracts (`SailConfigured`, `SailCodeMemoryCompatible`,
   program well-formedness) that are application-level premises no system table will discharge;
   they must remain explicit in the final public theorem type.
3. **Three completeness defects (R1–R3) found by the W4 rollout are fixed in source.**
   Carrying chips through the trace-generation layer exposed prover-side contracts
   stronger than the circuits require, plus one provider witness-generation policy that was too
   restrictive:
   - **R1.** `AddressOperation.Assumptions` now guards the non-reserved-address lower bound by
     `is_real = 1`, and all five load plus four store `ProverAssumptions` carry the same gate.
     Active rows still owe `2^16 ≤ address`; padding does not. The named regression
     `AddressOperation.assumptions_zero` proves the literal all-zero operation input satisfies the
     shared address subcontract. The nine event-level memory-table APIs remain unpadded, and no
     full memory-chip zero-row inhabitance theorem is claimed yet; constructing and proving those
     complete padding rows is part of the remaining ensemble-height work.
   - **R2.** `LoadByteChip.ProverAssumptions` now states the two AIR branches directly: on LB, `msb` is the
     selected byte's high bit; on LBU, `msb = 0`. Its completeness layer accepts both opcode 29 and
     32, and `highBitLbuEvent_proverAssumptions` witnesses a concrete well-formed LBU at address
     `0x10000` selecting `0xff`. Thus high-bit unsigned loads are no longer outside completeness.
   - **R3.** Provider multiplicity is now an explicit row input rather than a constant local
     witness.
     Byte, Range, and Program entries carry natural counts, admitting zero-multiplicity padding,
     unit occurrences, and aggregated `m > 1` rows. Memory init/finalize entries carry a `Bool`;
     their circuits retain `m * (m - 1) = 0`, preserving the signed-memory-balance invariant while
     making both padding and active rows reachable.
4. **Provider multiplicity source closure is executable and branch-build clean.**
   `SP1CleanTest/Audit/ProviderMultiplicity.lean` builds concrete tables through
   `Air.Flat.Table.build`, not hand-written row arrays. `bytePaddingTable_constraints` proves the
   retained padding row is accepted and `bytePaddingTable_busNeutral` checks its evaluated
   interaction multiplicity is zero. `byteAggregateTable_preservesMultiplicity`,
   `rangeAggregateTable_preservesMultiplicity`, and `programAggregateTable_preservesMultiplicity`
   check aggregate counts `7`, `9`, and `11`; their companion `*Table_constraints` theorems prove
   those generated rows satisfy the circuits. `memoryInitTable_booleanBranches` and
   `memoryFinalizeTable_booleanBranches`, again paired with constraint theorems, reach selectors
   `0` and `1` (the finalize pull evaluates the latter as `-1`). The integration regression goes
   beyond row reachability: one circuit-built Byte provider push at `+7` closes against seven unit
   pulls in the exact centered-integer per-key ledger, and the integer-to-Clean bridge proves the
   same list field-balanced. This prevents machine completeness from silently reverting to the old
   `0/±1`-only source contract. The current native canonical-closure theorem proves provider balance
   directly in the field, with no `ProviderMultiplicitiesFit` restriction; `NativeTraceFootprint`
   retains the actual interaction-count no-wrap bound `< p`. These
   named regressions pass in the full `lake test` target, and the complete main library builds with
   zero warnings or stray information output. The release axiom census is restamped only after the
   source commit; that restamp landed in `af6c8b11`, and `check_pins.sh` gates both snapshots'
   entry counts against their generated probes.
5. **No cryptographic claim.** Nothing here says anything about STARK soundness, FRI, LogUp/GKR,
   or Fiat–Shamir. The planned final form is probabilistic and lives in the ArkLib/VCVio
   integration: an executable `verifyCore` agreeing with the pinned Rust verifier, ArkLib
   knowledge soundness extracting a full AIR witness with an explicit error bound, and
   `sp1_air_sound` turning that witness into the Sail execution relation. The
   `FormalModel/Verifier.lean` boundary (a deterministic `PerfectExtraction` analogue with
   composition lemmas) is shaped for that seam. StarkWare's S-two verification (§11) is a
   concrete precedent for the layer immediately below `sp1_air_sound`: they formalize the LogUp
   lookup argument itself in Lean — the logarithmic-derivative counting lemma and explicit
   bad-set cardinality bounds quantifying the soundness error — while still treating the
   underlying circle STARK and the Fiat–Shamir randomness as assumed. That is exactly the
   intermediate abstraction our C2 obligation names (multiset balance ⇒ field-level LogUp
   soundness with an error bound), and their lemmas are a candidate model for how the ArkLib
   layer can discharge C2 rather than assume it.
6. **Native ensemble completeness has an explicit admissible semantic source** (§7.4): the
   proof-independent all-25 compiler constructs an AIR witness satisfying
   `SupportedCoreNativeRelation`; constraints, canonical provider closure, refresh placement, and
   all seven channel balances are proved.  Admissibility still records the per-chip event-validity,
   initial-Memory, Program-row projection, and actual-footprint facts not yet derived for
   a general bounded ordinary Sail execution. `NativeCompletenessNonVacuity.lean` jointly inhabits
   every premise in the zero-event canonical execution case; `ActiveNativeCompleteness.lean` joins
   one official Sail step to the exact JAL circuit event and the nonempty bounded native witness,
   without claiming full compiler-trace equality. Capacity alignment is closed; unconditional
   public-language equality now depends exactly on `NativeShardTraceTotal`.
7. **The extracted-to-native local ensemble transport is complete under named contracts; its global
   semantic refinement is not.** `SP1Clean/Composition/` composes every chip anchor with valid
   exact execution and separately authenticated memory-boundary witnesses, a caller-supplied
   `CanonicalPreprocessedInventory`, plus named preprocessing, memory-boundary, and public-limb
   transport contracts. Under those hypotheses it constructs the
   redistributed Byte/Range/Program providers, MemoryInit/MemoryFinalize, and both bump tables.
   `CoreEnsemble.lean` assembles those 55 native tables plus the verifier row and proves their
   complete local constraints. **R4:** the native provider suffix has all 17 Range widths `0..16`,
   closing the balance hole for honest shift rows that request widths outside `8/13/14/16`.
   **R5:** Byte/Range/Program counts are recounted from the actual Clean interactions of
   the verifier, 25 transported instruction tables, MemoryInit/MemoryFinalize, and both bumps
   rather than copied from the full exact cluster. The raw exact Byte/Range/Program assertion lists are empty.
   `CoreAIR.PreprocessedBinding` only records the named matrix/PCS-opening premise, to be discharged
   by ArkLib; it proves neither row-local meaning nor provider selection.
   `PreprocessedProviderContract` is the explicit caller premise for local semantics. Source main
   multiplicities are not reused and raw projected keys are not assumed unique. The caller-supplied
   inventory selects matching-block source-backed carriers, explicitly requires their projected keys
   to be `Nodup`, and may omit zero-demand raw keys. The recount contract separately requires
   nonzero Byte/Program-key coverage, nonpositivity, and canonical capacity. `freshRowsByKey` is
   declarative/regression-only. `Composition/Balance.lean` retains the payload-indexed
   exact-natural-balance→signed-integer theorem under `SmallMultiplicities`; the unused projected-key
   closure was retired because the full exact cluster is not the reduced native ensemble.

   `CoreArtifact.lean` deliberately stops at caller-supplied recount and global contracts rather
   than hiding the remaining work. The recount contract derives Byte (including Range) and Program
   integer balance; `ExactNativeGlobalContract` retains all-channel interaction-count bounds,
   State/Memory integer balance, and `SemanticBoundaryBinding`. There is no theorem jointly
   inhabiting those contracts with valid exact clusters. The exact/PCS integration must still
   construct and authenticate the source-backed canonical inventory and discharge nonzero
   Byte/Program-key coverage,
   consumer nonpositivity, canonical capacity, PCS/program identity, State/Memory balance, and the
   semantic boundary, including the public
   Range13-quotient→native Range16 lookup change, the raw `Global`→typed-Memory lowering and local
   cancellation, preprocessing/program authentication, memory-boundary meaning, and syscall facts.
   Consequently `CoreAIRRefinementObligations.executionCase` remains open, and the unqualified
   `sp1_air_refinement` / `sp1_air_sound` names stay reserved. Under an explicit syscall-free
   restriction (`Soundness/CoreAIRSyscallFree.lean`) four of the bundle's twelve fields are
   discharged and a fifth is reduced to an explicit decoder property.
8. **Trusted surfaces T1–T5** (§10), including the pinned git dependency graph — in which the
   Clean DSL is currently a fork (T5) — and the trace-battery provenance caveat (§4.3).
9. The AIR models the *supervisor-mode* Core profile; user-mode/mprotect table variants,
   precompiles, and the memory-protection chips are out of scope.
10. **Trap and exception executions are unrepresentable.** Taken jumps/branches to misaligned
   targets and misaligned memory accesses are unsatisfiable in the AIR (each chip forces the
   alignment its width requires, matching SP1's own executor), so every produced Sail segment
   is trap-free — the theorems never speak about trapping executions. Relatedly, jump/branch
   targets live in SP1's 3-limb PC space: a wraparound target at or above 2^48 is unsatisfiable
   in-circuit (a completeness restriction, not a soundness gap — no false row is provable).

This report describes the state of an ongoing verification, not an audit certificate. Findings
of the 2026-07 release-readiness audit — including everything disclosed above — were logged with
file-level citations in a findings log kept out of the release tree by design; retrieve
docs/audits/2026-07-release-readiness.md (no longer in the tree) from git history at commit
`14c926bd`.

## 13. Reproduction

```sh
lake build SP1Clean        # the main library: 0 errors, 0 warnings, 0 info notes
lake test                  # the conformance anchors (the only native_decide)
lake lint                  # curated environment linters
scripts/run_audit.sh       # pins + zero-deferral gates + per-theorem axiom census
```

Toolchain: Lean `v4.32.2` / mathlib `v4.32.2`; every dependency is an immutable git pin (the
generated Sail model is config-generated from pinned sources — T4). Extraction
regeneration requires a clean checkout of the pinned sp1 extraction branch
(`dtumad/lean-extraction`) and a Rust toolchain — see `docs/agents/extraction.md`. The
axiom census snapshot lives at `docs/snapshots/axiom-ledger.md`; regenerate before citing.
Report citations — every cited repo path and cited declaration name — are checked by
`scripts/check_report_citations.sh`, maintained documentation by `scripts/check_current_docs.py`,
the exact 25-chip release inventory by `scripts/check_release_surface.py`, and recorded pin values
by `scripts/check_pins.sh`. These run as gates inside `scripts/run_audit.sh` and in CI, so a stale
citation, missing chip artifact, or drifted recorded pin fails the build rather than surviving in
prose. (Quoted signature *text* is not machine-compared; the tree is authoritative.)
