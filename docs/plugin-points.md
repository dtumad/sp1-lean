# Plug-in points

Where a circuit plugs into the semantics core, what each seam demands of the circuit that plugs in,
which consumer above the seam can be reused after its contract is re-established. Current campaign
status and dependencies live in [the roadmap](roadmap.md); file references here identify the seams.

## The seams

| Seam | Where it plugs in | Contract an incoming circuit must meet | Reusable consumer | Work tracker |
|---|---|---|---|---|
| Operation gadget | `SP1Clean/Native/Operations/<Op>/Defs.lean` `main`, composed by `let _ ← Op.circuit ⟨…⟩` | identical `Spec` (`SP1Clean/FormalModel/Contracts/Operations.lean`) and assumptions, soundness and completeness (`SP1Clean/Proofs/Operations/<Op>/Formal.lean`), consumed channel contracts, computable/exportable witnesses, field-generic over the stated bounds | chip semantic proofs that use those contracts | Reusable gadgets [#16](https://github.com/dtumad/sp1-lean/issues/16); backend fixtures and verified replacement [#29](https://github.com/dtumad/sp1-lean/issues/29) |
| Reader | `SP1Clean/Native/Readers/*.lean`, Specs in `SP1Clean/FormalModel/Contracts/Readers.lean` | the bus interaction shape (a pull at the previous timestamp, a push at the row's own; `SP1Clean/Native/Readers/RegisterRead.lean:26–29`), the `SpecD` lifts | the chips and `ChipGroundingContracts` | Operand adapters [#16](https://github.com/dtumad/sp1-lean/issues/16) |
| Chip | `SP1Clean/Native/Chips/<Chip>/Defs.lean`; `ChipKind` (`SP1Clean/Soundness/ChipRow.lean:34–83`); the registry `allChipKinds` | Spec (`SP1Clean/FormalModel/Contracts/Chips.lean`), soundness/completeness, the Sail bridge packaged as `advance`, `ChipGroundingContracts` (`SP1Clean/Soundness/ChipContracts.lean`), `ChipFaithful` where the chip is SP1-faithful | the timed grounding engine, `supported_core_witness_grounding`, the compiler | Shared access gadgets and later alternative tables [#16](https://github.com/dtumad/sp1-lean/issues/16) |
| Provider / boundary table | positions 25–54 of `sp1Ensemble` (`SP1Clean/Soundness/SP1Ensemble.lean`); snapshot, ordered and final providers; `WritePermissionProvider` | the local table spec plus uniqueness/order facts (`SP1Clean/Native/Operations/OrderedBoundary.lean`) | Byte/Range/Program recount; memory boundary balance | Complete boundary installation [#12](https://github.com/dtumad/sp1-lean/issues/12); later provider alternatives [#16](https://github.com/dtumad/sp1-lean/issues/16) |
| Host receiver | `HostCallReceivers.available` (`SP1Clean/Soundness/HostCallReceivers.lean:83–85`, 20 installed) | the receiver Spec (for example `SP1Clean/FormalModel/Contracts/HostControl.lean:21–23`) plus the HostCall receipt discipline | `HostCallLedger`, the terminal receipt, host replay | WRITE, VERIFY and authenticated allocations [#12](https://github.com/dtumad/sp1-lean/issues/12) |
| Verifier extension | `ToClean/Air/VerifierExtension.lean` `ClosedVerifier`; `boundary.install` | a ledger-preserving install | everything below it | Complete outgoing snapshot and canonical header [#12](https://github.com/dtumad/sp1-lean/issues/12) |
| Machine | `Air.Flat.Realizes m ens boundary admissible` (`ToClean/Air/Realizes.lean`) | `SoundnessTarget` and `CompilerTarget` (`SP1Clean/Soundness/Shard/Contract.lean`) | `statement_iff` | First native realization [#12](https://github.com/dtumad/sp1-lean/issues/12); later RiscvAir instance [#16](https://github.com/dtumad/sp1-lean/issues/16) |

## Why the map matters

The [audit surface](audit-surface.md) distinguishes statement meaning from proof implementation.
A concrete ensemble in a theorem's type determines its circuit bodies, so those definitions can
be reachable even when the theorem does not spell them out. Keeping only a gadget's output `Spec`
does not establish substitutability: consumers also depend on assumptions, channel requirements
and guarantees, witness generation, and sometimes physical interaction footprints.

A replacement must re-establish those consumed contracts and both proof directions. The resulting
semantic statement can then remain unchanged while the accepted witness representation changes.
`ChipFaithful` separately compares complete assertion and interaction systems: an optimized gadget
that changes them needs a new chip-level comparison, or belongs to a separately identified native
ensemble. The resolution gate only checks declaration locations; it does not prove any of these
replacement obligations. Kernel proofs, exportability and conformance checks serve different roles.

The export and replacement directions share a contract. A lookup-free gadget's complete seam
contract can be packaged as a challenge. An external implementation is accepted after proving
the consumed obligations, with an integration regression checking the resulting machine claim.
These deliverables are tracked together in [#29](https://github.com/dtumad/sp1-lean/issues/29).

## The north star

A spec of RISC-V execution paths general enough that a zkGolf-style project can optimise the entire
arithmetization against it (#29). The challenge spec is `Realizes` for the RV64 machine; any
realizing ensemble is a submission; the native ensemble becomes the reference once its instance closes; the score
is the ensemble's cost under a fixed profile. Prerequisites, as checkboxes on the issue: `Profile`
as a structure, a closed `Realizes` instance, a cost model on `Air.Flat.Ensemble`, and the reference
submission's cost measured by that model.

See also [`architecture.md`](architecture.md) for module ownership, [`roadmap.md`](roadmap.md) for
the implementation order, and [`leanervm-comparison.md`](leanervm-comparison.md) for the second
machine that could target the same interface.
