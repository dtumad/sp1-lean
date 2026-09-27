# Presentation evidence for September 28

Ready to forward to the presentation agent. This answers the [updated handoff](request.txt) from talk revision `4a632e8`; [source provenance](talk-source.json) is included. The talk repository and its pins have not been edited.

| Result | Exact evidence revision | Start here |
|---|---|---|
| ADD and complete counter — [#100](https://github.com/dtumad/sp1-lean/pull/100) | `80092c9a0a2aea3db9db3066fba51018b095e628` | [Actual outputs, literal theorems, pins, commands and speaker paragraphs](examples/README.md) |
| Standalone backend conformance — [#104](https://github.com/dtumad/sp1-lean/pull/104) | `698bec03cf75327921a694c55a219d340a77ea47` | [Raw witness verdicts, costs, pins, commands and speaker paragraph](backend/README.md) |
| Joined branch example — [#106](https://github.com/dtumad/sp1-lean/pull/106) | `066d52a73e01c46e1df8fc4a155176ee59bc660d` | [Full Sail/compiler/local-row join, actual output, theorem and speaker paragraph](branch/README.md) |

These are separately identified evidence revisions. The backend is not part of a claimed combined integration commit. Every package includes actual captured output, prerequisites and cache conditions, with full logical/test/backend boundaries. [Independent review records](reviews.json) are separate from build validation.

## What the speaker can use

- **ADD:** the actual 89-table complete-Memory fixture accepts active ADD and the empty identity and rejects all seven mutations. Keep this assembly distinct from the retained 55-table theorem.
- **Counter:** the independent machine over field 97 has public states 0..15 and at most 15 increments. The executable compiler and universal raw-acceptance equivalence are complete. All 13 printed cases pass. The actual driver is `2→5` with three rows; the current schematic `3→5` is different. Keep the counter in backup.
- **Backend:** all 29 witness cases and 26 mutations give their expected outcomes. Twenty input witnesses accept and nine reject; five mutations accept and 21 reject. The package includes actual snarkjs rejection of a corrupted result and acceptance of the deliberately free zero inverse changed to 7. Costs 6/33/132 are measured full R1CS constraints over BN254, not optimization gains or a backend-correctness theorem. The zero adapters use the active gate.
- **Branch:** `BEQ x1,x2,+4092`, both operands zero, advances PC 65536→69628 and clock 1→9. The theorem joins full official Sail retirement to canonical projection, actual event compilation, the exact generated Branch row and local table constraints. The driver checks one real row, 46 cells and 50 flattened constraints. It computes compiler/row facts; the full Sail step is theorem evidence. This is local chip acceptance, without assembled provider/channel balance or general compiler completeness.

The branch supplements the same-value-store review example. The earlier narrowing of +4092 to −4 belonged to the fork's semantic event compiler.

## Validation and source history

ADD/counter and backend outputs were freshly reproduced from their exact clean reviewed heads using warm caches. Their successful historical full CI is linked, with actual PR merge-checkout provenance where applicable. Historical local gates are labelled separately; cancelled/skipped checks are never reported as passing.

The branch passed strict full builds, core tests, both lint scopes, both trust audits, byte-identical export regeneration, all 857 Rust differential rows, parsed driver output and literal theorem/axiom inspection. The full gates ran at integrated revision `70b73fa3`. Concurrent rebasing of #103 required a history-only merge to the published `066d52a7`: both have exactly the same complete tracked tree, `4be4c9f840b1d30c707525ed8a1df66c6852d8cb`. A final strict full build and parsed driver also passed at the published clean head. [The integration record](branch/history-only-integration.json) makes that distinction explicit.

The example files are byte-identical to their independently reviewed initial commit. The final diff against compiler base `112eb5d8` contains exactly the fixture and driver. New production interfaces, semantic restrictions, dependency pins and trust exceptions were unnecessary.

## Current PR status

Captured **2026-09-27 22:13:33 UTC** in [current-pr-status.json](current-pr-status.json):

- #99, #100, #101 and #102 are merged.
- #103 at `112eb5d8` and #104 at `698bec03` have passing full alignment CI and remain open.
- #106 at `066d52a7` is open, stacked on #103, with `ci:alignment`. Local validation passed; guards passed and CI build is running. Full alignment CI is pending, not claimed passed.
- Earlier PR snapshots remain included for provenance; [concurrent updates](concurrent-pr-updates.json) record the stack's intervening rebases.

The existing Sail/host owner retains the remaining endpoint work. The general compiler campaign continues with I-type/ALU-type/U-type/x0 validity. These artifacts do not establish the full SP1 realization or exact upstream/cryptographic refinement.

The presentation agent selects reviewed evidence, updates pins/snippets/wording together and rebuilds the deck. Evidence cutoff remains four hours before the 8am talk; deck freeze remains three hours before. The priority 1 archive is an earlier immutable delivery containing the ADD/counter and backend packages; the final archive contains this directory including the branch follow-up. All packaged files are covered by the top-level `SHA256SUMS`.
