# Adding or migrating a chip

Start from the released SP1 revision in [provenance](../../scripts/provenance.json), the pinned
Clean guides named in [AGENTS.md](../../AGENTS.md), and the [local proof notes](proof-patterns.md).
Read the source AIR, column layout and witness construction together. An unchanged AIR does not
establish unchanged loader, host or executor behavior.

## 1. Define the semantic contract

Put pure arithmetic and architectural meaning below the circuit implementation, under
Semantics/Specs or the relevant Model contract. Reuse native column types in Circuits/Types.
Keep field bounds, clock/address representability and inactive-row freedom explicit.

Separate the public semantic Spec from structural assertion evidence. A witness recipe is not
a specification. Do not add compatibility wrappers when the migration can update every
in-repository consumer.

## 2. Build the circuit and witnesses

Use Clean's bundled child circuits for arithmetic, CPUState and register/Memory access.
Let the parent own its opcode selectors and derive activity where that matches the source.
Keep reader clock inputs, write values and gating consistent with the actual instruction.

Use Clean's exportable witness IR and typed input/hint machinery. Compose repeated operations
through their interfaces; preserve expression sharing. Native-only closures, parallel emitters,
interpreters and schedulers are not integration shortcuts.

Prefer local Inputs/Columns, witness and implementation modules with a public bundled interface.
Use `GeneralFormalCircuit` when honest construction needs stronger assumptions than soundness;
use `FormalAssertion` for a supplied block with no generated output.

## 3. Prove local meaning and construction

Start soundness/completeness with `circuit_proof_start`, pass explicit elaborated metadata and
prefer default obligations supported by focused `circuit_norm` lemmas. Prove the semantic
relation from child Specs and local arithmetic; retain padding and inactive-row domains.

Separate a reusable arithmetic lemma from a large circuit context when both proof directions
need it. Keep witness values opaque across expensive normalization. Do not raise budgets or
replace kernel checking with native computation.

## 4. Connect execution and physical assembly

Provide the Sail bridge, native row contracts, event-to-input construction and completeness
realization where the instruction's scope requires them. Register identity/order and constructors
through the canonical instruction registry; migrate all exhaustive consumers.

Machine grounding must account for actual Program, State and Memory traffic. Reuse the canonical
typed ledger, physical table inventory and chronological compiler. Repeated keys, zero
multiplicities and occurrence/row bounds must survive every projection.

A new host effect also needs authenticated source/target observations, host state and memory
effects. Installation of an isolated handler is not complete mixed-execution soundness.
Preserve every obligation in the [capstone contract](../../SP1Clean/Soundness/Shard/Contract.lean).

## 5. Compare the generated Rust

Add the component to the existing Clean export fixtures and independent Rust comparison suite.
Use released SP1's typed columns, `MachineAir::generate_trace`, AIR evaluation or executor effects
as appropriate. Compare the full row and interaction ledger, including padding, and normalize
only documented representation differences.

Exercise meaningful malformed rows, public values, permissions, counts and shapes.
Keep source-side inventory independent of native generation so an exporter cannot authenticate
its own omissions. Update the [coverage record](../../rust/sp1-comparison/inventory/coverage.json)
with honest scope limits: native semantic proofs, released-component tests, backend tests and
uncovered behavior are separate claims.

Statically optional mode-associated columns require exact zero/payload-width representations.
Passing supervisor comparisons with the mprotect Cargo feature does not implement user-mode
semantics.

## 6. Validate and retire superseded code

Index production modules in SP1Clean.lean and, when core, SP1Clean/Core.lean. Keep tests outside
production imports. Run the checks in AGENTS.md, including fresh ensemble AIR/witness exports
for integration changes. `scripts/check_release_surface.py` checks all 25 instruction registration,
formal/bridge/completeness and non-vacuity entry points.

Rebuild the affected consumer closure and finish with strict full builds, lint and both trust
scopes. Review performance at the consumers, not only the edited proof. Update tracking issues
with evidence and remaining gaps; keep durable documentation concise.

Once every live consumer and comparison has migrated, delete the superseded implementation and
its dedicated machinery. Preserve useful mathematics and native proofs. Rust differential tests
do not establish formal lowering correctness or cryptographic verifier soundness.
