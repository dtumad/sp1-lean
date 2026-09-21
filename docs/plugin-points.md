# Plug-in points

Where a circuit plugs into the semantics core, what each seam demands of the circuit that plugs in,
which consumer above the seam stays unchanged, and where current work sits on that map. Presented at
the 2026-09-21 talk; tracked as fork issue #24. Line references are to the tree at `6bd1cd50`.

## The seams

| Seam | Where it plugs in | Contract an incoming circuit must meet | Consumer that stays unchanged | Current work here |
|---|---|---|---|---|
| Operation gadget | `SP1Clean/Native/Operations/<Op>/Defs.lean` `main`, composed by `let _ ← Op.circuit ⟨…⟩` | identical `Spec` (`SP1Clean/FormalModel/Contracts/Operations.lean`), soundness and completeness (`SP1Clean/Proofs/Operations/<Op>/Formal.lean`), `ComputableWitnesses`/witgen, `#assert_exportable`, field-generic over `2 ^ 17 < p` | every chip `main` that composes it; chip proofs apply the Spec by field | Circom/R1CS on lookup-free gadgets (#27); zk.golf export/import (#25, #26); RiscvAir M1 lifted gadgets (#16) |
| Reader | `SP1Clean/Native/Readers/*.lean`, Specs in `SP1Clean/FormalModel/Contracts/Readers.lean` | the bus interaction shape (a pull at the previous timestamp, a push at the row's own; `SP1Clean/Native/Readers/RegisterRead.lean:26–29`), the `SpecD` lifts | the chips and `ChipGroundingContracts` | RiscvAir M2: one parameterised operand adapter instead of six readers (#16) |
| Chip | `SP1Clean/Native/Chips/<Chip>/Defs.lean`; `ChipKind` (`SP1Clean/Soundness/ChipRow.lean:34–83`); the registry `allChipKinds` | Spec (`SP1Clean/FormalModel/Contracts/Chips.lean`), soundness/completeness, the Sail bridge packaged as `advance`, `ChipGroundingContracts` (`SP1Clean/Soundness/ChipContracts.lean`), `ChipFaithful` where the chip is SP1-faithful | the timed grounding engine, `supported_core_witness_grounding`, the compiler | RiscvAir M2–M4 tables per family; `Memory.Access width` replacing eight load/store chips (#16) |
| Provider / boundary table | positions 25–54 of `sp1Ensemble` (`SP1Clean/Soundness/SP1Ensemble.lean`); snapshot, ordered and final providers; `WritePermissionProvider` | the local table spec plus uniqueness/order facts (`SP1Clean/Native/Operations/OrderedBoundary.lean`) | Byte/Range/Program recount; memory boundary balance | outgoing-boundary checks installed as circuits (#12 item 3); 23 provider tables → bit decomposition plus one static table (#16 M2) |
| Host receiver | `HostCallReceivers.available` (`SP1Clean/Soundness/HostCallReceivers.lean:83–85`, 20 installed) | the receiver Spec (for example `SP1Clean/FormalModel/Contracts/HostControl.lean:21–23`) plus the HostCall receipt discipline | `HostCallLedger`, the terminal receipt, host replay | WRITE, VERIFY, authenticated allocations (roadmap "full host inventory") |
| Verifier extension | `ToClean/Air/VerifierExtension.lean` `ClosedVerifier`; `boundary.install` | a ledger-preserving install | everything below it | the complete outgoing snapshot verifier and canonical header |
| Machine | `Air.Flat.Realizes m ens boundary admissible` (`ToClean/Air/Realizes.lean`) | `SoundnessTarget` and `CompilerTarget` (`SP1Clean/Soundness/Shard/Contract.lean`) | `statement_iff` | `Profile` as a semantic resource structure (#12 item 1); the mixed compiler (#12 item 4); RiscvAir M2 `Realizes` inhabited (#16) |

## Why the map matters

The headline theorems' statements never mention a gadget or chip body. `docs/audit-surface.md`
records the split: everything reachable from a theorem's *type* can make it say the wrong thing,
everything only in its *proof* is kernel-checked. A plugged-in circuit is consumed only through
its seam contract (Spec, soundness, completeness, witness computability, and for chips the bridge
and grounding contract). Replacing the circuit while keeping the contract therefore changes nothing
above the seam, and the existing gates (`scripts/check_audit_surface.sh`, the axiom census, the
exportability battery, the dump-anchored witgen gate for SP1-faithful chips) are what make the
replacement trustworthy.

The same fact makes the two zk.golf directions symmetric. Export (#25): a gadget seam's contract
(types, input assumptions, Spec) is exactly a zkGolf-style challenge. Import (#26): an externally
produced circuit is accepted at the gadget seam under the same contract, and a machine-theorem
invariance regression checks that nothing above the seam moved.

## Current work, by seam

- Machine: `Profile` is a bare predicate with no default; `SoundnessTarget` and `CompilerTarget` are
  unfilled (#12 items 1 and 4). RiscvAir M2 is the first planned `Realizes` instance (#16).
- Verifier extension: complete supplied-target equality is open; `MemorySnapshot.checkFinal` and
  change coverage are not yet installed as circuits (#12 item 3).
- Host receiver: WRITE and VERIFY receivers are not installed; allocations are not authenticated.
- Provider / boundary table: the outgoing checks above; RiscvAir replaces the 23 Byte/Range tables.
- Chip: RiscvAir M2–M4; the three execution carriers still have only a per-step bridge (#12 item 5).
- Reader: RiscvAir M2's operand adapter.
- Operation gadget: the circom/R1CS integration test (#27) and the zk.golf pair (#25, #26).

## The north star

A spec of RISC-V execution paths general enough that a zkGolf-style project can optimise the entire
arithmetization against it (#29). The challenge spec is `Realizes` for the RV64 machine; any
realizing ensemble is a submission; the SP1-shaped ensemble is the reference submission; the score
is the ensemble's cost under a fixed profile. Prerequisites, as checkboxes on the issue: `Profile`
as a structure, a closed `Realizes` instance, a cost model on `Air.Flat.Ensemble`, and the reference
submission's cost measured by that model.

See also [`architecture.md`](architecture.md) for module ownership, [`roadmap.md`](roadmap.md) for
the implementation order, and [`leanervm-comparison.md`](leanervm-comparison.md) for the second
machine that could target the same interface.
