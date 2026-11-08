# Clean extensions and upstream integration

The active Clean revision is owned by lakefile.toml and lake-manifest.json. Local additions live
under ToClean in the namespaces they would occupy upstream, with their missing upstream capability
described in each module docstring. No SP1 imports are permitted there.

Prefer an extension to a fork. Fork only when a canonical declaration must change and downstream
additions cannot express the required behavior. Keep that patch minimal, tied to its upstream
proposal, and delete it when a compatible upstream version supplies the change. Do not maintain
duplicate implementations or compatibility wrappers after consumers migrate.

## Existing gaps

| Addition | Purpose |
|---|---|
| WitnessGenerationData | Honest witness construction at arbitrary committed data; upstream reference/honesty theorems still specialize to empty data |
| ComputableWitnesses / Equality | Zero-cell assertions need no input or environment agreement; remove these transport laws when upstream supplies them |
| TableBuild / EnsembleBuild | Typed row/table/ensemble construction with actual ledger and verifier proofs |
| EnsembleCheck / FiniteLookup | Authenticated finite lookup inventory and executable raw-witness acceptance |
| Realizes / CompleteEnsemble / EnsembleCompiler | Machine interpretation and constructive equivalence interfaces |
| Receipt / PublicVerifier / projection helpers | Preserve original circuit/ledger behavior across actual composed consumers |
| Guarded | Boolean activity for bundled circuits, preserving witness programs and all physical interaction occurrences; remove when Clean supplies this interface |
| OneHot / VariableRange / ExpressionSum | Decode a bounded index and prove a runtime unsigned-width bound using ordinary Clean witnesses and constraints |

These are reusable additions, not alternate SP1 semantics. Their concrete consumers determine
whether an abstraction earns its place. When upstream accepts an API, migrate imports and delete
the local copy.

Clean #503 supplies canonical data/hint agreement, taking over #450. Clean #426 bundles witness
computability into formal circuits and assertions. Chip and table construction consume those
bundles; standalone chip computability proofs and their composition bridge are retired. Prefer
the upstream default tactic, with explicit metadata and focused evaluation lemmas for large
structured outputs. The arbitrary-data honesty extension remains additive; bundled computability
does not establish final-data agreement or complete ensemble witness generation.

## Built-in Rust export

Clean #445/#446 supply direct generated Rust AIR/witness programs, fixed columns and runtime
prover inputs. The selected version must be reconciled with this repository's toolchain and module
system. Use those APIs for AIR and witness export; the bespoke JSON interpreter is retired.

Representation changes to canonical Component/Ensemble/Witgen objects may need an upstream patch;
new adapters and supporting lemmas belong in ToClean. Scheduler support is not scheduler
completeness or final-data agreement. Preserve those proof obligations explicitly.

The selected upstream main revision supplies typed routing, public-input/table-height statements,
empty dynamic tables, reusable proving keys (#501), and shared component printing (#502).
No Clean fork patch remains in the dependency graph. Empty tables retain their physical inventory
positions; only nonempty AIRs enter the Plonky3 batch. Fixed heights remain mandatory.

The Lean and Rust backend pins must identify the same immutable revision. Complete an upgrade's
strict builds and fresh export/comparison checks before selecting another upstream batch. Open
#494 (resource histories and closed channels) and #480 (generator completeness) are follow-up
candidates, not capabilities assumed by this pin. In particular,
channel-level guarantees do not replace exhaustive SP1 execution and mutable-resource grounding.

See [export](../export.md) and #28/#29 for the integration contracts. Scheduler completeness,
final-data agreement, and correctness of printed Rust remain separate obligations.
