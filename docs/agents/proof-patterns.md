# SP1 proof notes

Read the pinned Clean proving guide, performance guide, witness-authoring guide and AIR README
listed in [AGENTS.md](../../AGENTS.md) first. These notes cover SP1-specific composition and
representation pitfalls. Upstream owns the general circuit and extraction APIs.

## Semantic and circuit boundaries

State arithmetic, register effects, clocks and memory meaning in a semantic Spec. Keep raw
assertion equations as implementation evidence, with a proved connection to that Spec.
Compose `FormalCircuit`, `GeneralFormalCircuit` and `FormalAssertion` interfaces; a plain
Circuit does not provide the same proof boundary.

Start soundness and completeness with `circuit_proof_start`. Normalize the resulting child
Spec hypotheses with targeted `circuit_norm` lemmas before assembling the parent conclusion.
Do not unfold a child's implementation merely to reconstruct facts its bundle already supplies.

Keep soundness assumptions distinct from honest-constructor assumptions. A selector constrained
binary by the circuit belongs in its proved Spec; completeness may require the supplied selector
to be binary. Preserve inactive rows' actual freedom. In particular, inactive commitment bitmaps
need not be Boolean or one-hot.

For a factored bundle, pass explicit elaborated metadata. Prefer Clean's default obligations,
adding missing `circuit_norm` lemmas for output, length and channel projections. The bundled
`circuit.localLength` and an elaborated length projection are different expressions: provide
the rewrite matching the consumer. Measure affected consumers before replacing a working explicit
obligation with a default that unfolds a larger circuit.

A composing chip normally keeps the output returned by its `main`. Its child outputs may occupy
noncontiguous offsets; replacing this with a single `varFromOffset` can be incorrect.

## Witness representation and sharing

Use Clean's witness IR and typed hint interfaces. Do not add Lean closures that the exporter
cannot serialize, or a second evaluator/scheduler to work around an unsupported construct.
Witness generation proves neither final-data agreement nor general completeness by itself.

A deeply nested column structure can make flattening expensive. Compose its smaller bundled
blocks where they are actual reusable proof boundaries. When witnessing a modest structured
block directly, `fromElements` lets `toElements_fromElements` expose the flat vector without
reducing a tower of nested appends. This is a representation choice, not permission to bypass
the bundled subcircuit interface.

Keep repeated witness expressions shared. A serializable expression may still duplicate a large
tree. Preserve the DivRem export-size and sharing regression when changing its witness helpers.

## Field, word and arithmetic seams

- `Word` is a Vector abbreviation. Use `Word.toBitVec64 w` when dot notation cannot find the
  intended namespace.
- Normalize `a + -b` versus `a - b` deliberately before matching gate hypotheses. Use
  `eq_of_sub_eq_zero` when a concrete equality will fix a helper lemma's metavariables.
- Prefer the existing Boolean-from-gate lemmas for ZMod selectors. Generic field lemmas can
  encounter different ZMod instances during elaboration.
- Give `ZMod.val_natCast_of_lt` a concrete value and modulus bound before asking arithmetic
  automation to solve it. An uninstantiated inequality is not a usable arithmetic goal.
- For div/mod reconstruction, prove the natural-number identity first, lift it to the field,
  then use `linear_combination`. Rewriting a field identity through `val` can expand the wrong
  terms.
- A gate `m * k - a = 0` proves `a = m * k` with the negative coefficient in
  `linear_combination`.
- Use `ring1` in a tactic alternative that must fail when it cannot close the goal.
  Normalization-only success can otherwise prevent later alternatives from running.
- Prefer targeted `simp` on the relevant hypotheses. Use only simp arguments that actually
  fire; strict package lint treats unused arguments as failures.
- Factor shared arithmetic dispatch into lemmas over small, explicit field arguments. Match
  the public Spec's conclusion so callers need no large normalization bridge.
- Reuse the word sign-extension and carry lemmas in the arithmetic layer. W-instruction shifts
  use five shift bits; full-width shifts use six. Preserve that distinction in Sail bridges.

For environment projections, pass a concrete Fin index, such as `⟨k, by omega⟩`, when an
implicit numeral creates an unreduced coercion. Normalize witnessed-block projections before
`exact`; otherwise elaboration may attempt a large definitional-equality reduction.

## Channels, padding and physical data

Byte/Range checks use the Byte channel with the raw message and a gated multiplicity.
Do not replace this with an unconditional range assertion on a multiplied payload: padding
and zero-multiplicity rows have different obligations. SP1 and native Clean use opposite
Memory/Program orientations; comparison adapters explicitly negate those channels.

Native soundness consumes the canonical typed Clean ledger. Use compositional interaction
recovery and projection lemmas rather than a second hand-written ledger. Preserve every physical
occurrence, including repeated keys and zero counts. The occurrence bound is independent of
which rows happen to have nonzero multiplicity.

Source/target snapshot membership, ordered access chains and host observations are separate
boundaries. Memory balance alone does not authenticate a snapshot, establish an execution order,
or identify the latest write without its grounding hypotheses.

A table stores its evaluation data and a physical row bound. Changing stored data can preserve
decoded rows and literal interactions while changing a data-dependent semantic predicate.
Prove the required agreement at the actual environments. A subset of tables does not determine
the original ensemble's complete canonical data.

An empty dynamic table and a nonempty table's padding are different cases. Power-of-two padding
must satisfy that component's constraints and ledger contract; zero input is not universally
valid. Do not restrict valid execution counts to avoid constructing honest padding.

Keep one complete Sail/host/clock transition. Finite snapshots, realized Sail states, events and
physical rows have distinct meanings. Resource bounds must come from the stated semantic
domain and actual circuit inventory, never an added caller readiness premise.

## Performance and validation

Keep expensive values opaque, hypothesis types folded and shared expressions shared.
A helper over a large definition can still unfold it during type checking; abstract the expensive
argument itself. Removing `by exact` can remove a useful opacity barrier even for a proof field.
A locally faster proof can make downstream consumers slower.

Measure the changed dependency closure with the package options. Keep transcripts in PR artifacts;
do not retain timing tables here or repeat a failed experiment without new evidence. No budget
increase, proof deferral or kernel-check bypass is a performance fix.

Build edited dependencies before inspecting dependents with the LSP or `lake env lean`.
The latter does not rebuild dependencies and may exit zero after a stack overflow. Require
complete expected output as well as a successful exit. Finish with the strict full build and both
compiled trust scopes; source checks do not establish compiled trust.

Check running builds first, use one heavy build at a time, and preserve the measured child-Lean
settings. `LEAN_NUM_THREADS` controls Lake's pool; there is no Lake `-j` flag. Server workers
and build workers have different command lines. Never kill `lean --server` or `lake serve`.

For a slow proof, inspect a process sample before attributing a pause to a hang. An unfinished
module does not appear in Lake's completed-job list, and a stable memory footprint is not
evidence either of progress or deadlock.
