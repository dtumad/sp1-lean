# leanerVM comparison

Source review at leanerVM commit
[`4b95a607`](https://github.com/Verified-zkEVM/leanerVM/tree/4b95a607259f9a253083c6f2f1afefcb9fadabe3),
10 September 2026. The review also covered the bus experiment at PR 17 head
[`a01059aa`](https://github.com/Verified-zkEVM/leanerVM/tree/a01059aace5e62c68ac018eeabed706bea8329e9)
and the protocol proposal at PR 15 head
[`716d9103`](https://github.com/Verified-zkEVM/leanerVM/tree/716d910388de9a0f8ae4c6c95baa085f5dfbf6fb).
This is a source review, not an independently reproduced leanerVM build. Draft interfaces and
blueprint theorems below are not reported as completed verification.

## What is implemented

| Boundary | leanerVM at the reviewed commit | This development |
|---|---|---|
| ISA | Six instructions over a binary field, with field-valued PC and frame pointer | SP1's supported RV64 instruction chips, bridged to official Sail |
| Memory | A fixed, nondeterministically chosen write-once image; instruction execution checks its cells | Mutable byte RAM and integer registers, with timed per-location bus grounding |
| Execution | Defined `execute`, `step`, fuelled `run`, and `ValidExecution` with initial/final public boundaries | Ordinary Sail execution and explicit syscall events; complete native boot-to-HALT integration remains open |
| Decoding | Exact eight-field bytecode decoder with a proved encode/decode characterization | Executable image decoder, proved uniform Sail agreement, and authenticated fixed Program circuit |
| AIR | Bytecode representation; opcode AIRs and the full ensemble remain blueprint work | Proved instruction AIRs, native provider circuits, and an existing conditional machine theorem |
| End-to-end direction proofs | Planned AIR/execution correspondence | Native grounding and a restricted constructive compiler are proved; the unrestricted bounded core bundle is not instantiated |
| Execution/export | Semantic memory reads and execution are currently noncomputable | Executable row constructors and exported witness programs; generic event routing/provider assembly remains open |
| Rust correspondence | No completed whole-VM faithfulness proof in reviewed main | All 25 supported instruction chips have whole-chip faithfulness proofs; exact system-table refinement remains separate |

The execution distinctions follow from
[`Execution.lean`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/LeanerVM/Semantics/Execution.lean),
[`Step.lean`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/LeanerVM/Semantics/Step.lean),
and [`Memory.lean`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/LeanerVM/Semantics/Memory.lean).
The exact decoder theorem is in
[`Bytecode.lean`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/LeanerVM/Arithmetization/Bytecode.lean).
Implementation status and proposed layers are distinguished in the
[`status`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/docs/roadmap/leanisa-status.md)
and [`blueprint`](https://github.com/Verified-zkEVM/leanerVM/blob/4b95a607259f9a253083c6f2f1afefcb9fadabe3/docs/roadmap/leanisa-blueprint.md).

## Lessons for the capstone

**Keep the public execution relation small and independent.** leanerVM's semantic boundary can be
read without its AIR implementation. Our target remains the same kind of presentation: checked
program/host data, bounded local execution between complete boundaries, and a raw Clean statement
equivalent to that relation. Boot-to-HALT is an endpoint corollary. Their proposed `SatisfiedBy`
also carries seed/bytecode identity, row-index, capacity,
and count conditions outside raw ensemble satisfaction. It would not discharge our outstanding
provider or totality obligations merely by adopting that interface.

**Test missing hypotheses with concrete counterexamples.** Their review exposed a sentinel-JUMP
case where balanced steps do not imply the intended final execution, and disconnected padding
cycles that invalidate a reachable-state channel guarantee. Their planned correctness statements
now name bytecode conditions for sentinel exclusion and fill blocks. For our core, retain negative
controls for terminal behavior, disconnected or duplicated providers, full-message balance,
resource limits, and actual exported compilation. Passing arithmetic rows alone is insufficient.

**Share graph lemmas at their real common boundary.** A balanced graph can contain a source-to-sink
trail and additional cycles. leanerVM permits suitable padding cycles in its proposed assignment
relation. SP1's strict clock ranks must exhaust real instruction rows to ground mutable RAM.
Generic balance/trail lemmas are plausible shared code; the ranked grounding theorem and its
memory argument must remain explicit here.

**Do not generalize prime-field buses to binary fields by changing a type parameter.** In the
[bus experiment](https://github.com/Verified-zkEVM/leanerVM/pull/17), State pulls have trivial local
guarantees; authenticated Memory and Bytecode are separate planned boundaries. Its kernel-checked
[channel regressions](https://github.com/Verified-zkEVM/leanerVM/blob/a01059aace5e62c68ac018eeabed706bea8329e9/tests/LeanerVMTests/Arithmetization/Channels.lean)
demonstrate the characteristic-two obstruction tracked in
[issue 16](https://github.com/Verified-zkEVM/leanerVM/issues/16): `-1 = 1` collapses Clean's signed
pull/push distinction, while its interaction-count bound uses the characteristic, not field
cardinality. Nontrivial binary-field buses need explicit direction and natural multiplicities,
with a separate theorem connecting any field-sum encoding. Our current prime-field proofs are not
blocked by this issue; neither their generic syntax nor our Rust field interface establishes a
binary-field implementation.

## Decisions

A focused follow-up on 13 September 2026 checked main at
[`849806e7`](https://github.com/Verified-zkEVM/leanerVM/tree/849806e74f149139764f49061ce34c57c7967ba7),
which includes the bus-channel PR. Its execution model already supports arbitrary-start `run` and
proves `run_add`/`run_prefix`; its public `ValidExecution` still fixes the initial and terminal
registers. The AIR blueprint's closed-walk padding and whole-machine correspondence remain planned;
the protocol blueprint explicitly leaves recursion/aggregation to later work. No completed
shard-composition interface was found. Our existing pinned PolyFun finite-prefix interface is
sufficient for local semantic paths; the native capstone now includes explicit-boundary shard
composition, while succinct commitment authentication remains a later adapter. The substantive
additional obligation is complete RAM/host-state continuity, not a new path library.

For this capstone, retain the audited Clean/Lean/Sail pins and finish authenticated provider
closure, host footprints and terminal semantics, compiler totality, and whole-core export. Use the
comparison to guide focused counterexample regressions and small proof/API simplifications.
Do not add a leanerVM dependency, a shared VM framework, or a binary-field backend. Their reviewed
Lean 4.33.1/Clean pin differs from ours; a dependency update does not close these theorem gaps.

After the capstone, candidate contributions are:

- Mathlib-only graph/trail foundations from `Soundness/Walk.lean` and the field-independent
  endpoint-balance argument, with strict-rank exhaustion as a separate addition.
- Generic Clean table/ensemble construction, `CompleteEnsemble`/`EnsembleCompiler`, physical
  transition views, and export correctness interfaces already isolated under `ToClean/`.
- Joint review of explicit bus direction and multiplicity APIs before promising binary-field reuse.

Review each against then-current upstream APIs and the existing
[Clean contribution queue](agents/clean-upstream.md). Fixed-column and window-component proposals
may eventually simplify integration, but draft APIs are not a reason to rebase this capstone.
Keep SP1's Sail configuration, mutable-memory timing, host policy, and Rust oracle boundaries local.
The [protocol proposal](https://github.com/Verified-zkEVM/leanerVM/pull/15) is useful coordination
material for later ArkLib work; it supplies no cryptographic soundness theorem for this core.
