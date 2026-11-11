# Lean and Sail dependencies

The authoritative Lean graph is lakefile.toml, lake-manifest.json and lean-toolchain.
External generator inputs are in [provenance.json](../../scripts/provenance.json).
No path dependencies or moving branches; update one Lake requirement at a time.

Keep every dependency shared with Clean at the revision in the pinned Clean manifest.
CompPoly remains inherited from Clean; upgrade it through Clean rather than adding a root
override. Independent PolyFun or Sail updates must preserve this shared dependency graph.

A commit must be reachable from a published branch/tag: a warm local git object can hide a pin
that a fresh Lake clone cannot fetch. Validate a changed pin in a clean checkout.

The generated LeanRV64D model and Sail runtime are a compatible pair. Updating one can invalidate
generated namespaces, memory result types and every symbolically reduced proof. Regenerate through
[the owned pipeline](sail-model-provenance.md), never by editing generated Lean.

## Temporary choices

| Choice | Reason | Exit |
|---|---|---|
| Module-mode Sail pair | Runtime #13 and generator #1742 supply module support; supplementary namespace openings follow the generated declarations | Consume compatible upstream revisions after those changes merge |
| Chunked Sail variants | Lean 4.35 rejects the instruction variant’s flat constructor layout | A pinned Lean/compiler pair that accepts the flat layout, with full model and pattern-match validation |
| LeanRV64DRvfi library / legacy do | Avoids exponential discarded-action elaboration in generated RvfiDii | #6: pinned Lean/backend fix, regenerated/validated model and measured build |
| Non-module SP1 consumers | Handwritten visibility migration follows the prepared module-mode Sail pair | #33: complete consumer migration and public/private trust checks |
| Disabled Sdtrig retirement | Upstream checks an internal trigger-write marker even when the extension is absent; the model patch preserves arbitrary unrelated registers | Consume an upstream revision that makes disabled trigger retirement independent of trigger bookkeeping |
| Current toolchain | The pinned Clean/PolyFun/Sail graph must be validated together | Deliberate coordinated compatibility review; never bare lake update |

## Useful proof details

Sail.ArchSem owns the effect monad and sequential interpreter. `SP1Clean.runSail` specializes
that interpreter to the generated architecture. State effects are compared after interpretation;
reordering writes is not an equality of the free-monad action syntax. Prefer generated LeanRV64D
shims and upstream composition laws when reducing executions.
Narrow imports keep generic arithmetic independent of the full Sail/Mathlib closure.

Sail's global integer tokens can capture adjacent identifiers beginning with i: write a space
after arithmetic operators. Lean module mode does not justify changing arithmetic meaning to
avoid a parsing issue.

Memory proofs require explicit configured-state hypotheses, including disabled pointer masking,
MPRV and PMP entries. These are semantic assumptions, not axioms to add to the trust policy.
The generated device configuration and its rationale are documented with the pipeline.

After a dependency change, finish with the strict full library/test build and compiled trust
checks. A standalone lake env lean invocation does not refresh dependent oleans.
