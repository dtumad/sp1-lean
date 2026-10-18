# Export and integration

Lean owns native circuits, their Specs and their correctness proofs. The target integration is:

```text
Lean semantics → proved Clean circuits/witnesses → Clean Rust export → Rust/SP1 comparison
```

Use Clean's existing AIR extraction IR, lowering, Rust emitter and Witgen IR. Keep only thin
SP1 field/trait/event/layout/channel adapters. Do not grow another emitter, wire format,
interpreter or scheduler.

## Current facilities

- Circuit witnesses use Clean IR and its built-in serializer. Large expressions share operands
  through Clean's `Witgen.M` authoring API.
- ToClean's finite checker authenticates fixed lookup inventories and
  connects executable checks to raw Clean assertions and channel balance, including the public
  verifier and occurrence capacity.
- The whole-ensemble fixture uses Clean's built-in Rust exporter and backend. Verifier-fixed
  columns replace its legacy lookup; fresh Rust witnesses are compared with Lean reference rows,
  and backend proofs exercise public binding, row constraints and rejected mutations.
- The complete installed 94-table assembly exports through the same path. Active-branch and
  empty-local-segment fixtures supply instruction and boundary inputs through Clean hint tables;
  its scheduler generates the provider rows. Rust compares every row and ledger occurrence,
  including empty table positions, and exercises proof acceptance and endpoint/row mutations.
  The empty segment retains its ordered, bank and Exit terminals; removing any one is rejected
  by the backend. These finite cases do not prove general execution-generation completeness.
- The complete native opcode alphabet, including unsupported instructions, is compared with every
  constructor and discriminant of the released Rust enum. Lean's derived constructor names and
  native discriminants export as metadata; no Rust source parser or generated Lean enum is needed.
- All 25 supported instruction families export through the same built-in path. Rust compares
  generated witnesses, local constraint satisfaction and complete
  interaction multisets with SP1 v6.9.0's supervisor AIR, including padding and column mutations.
  Multi-opcode components use explicit selectors without hints. Comparisons retain repeated and
  zero-multiplicity messages, including the multiplication gadget's caller-supplied result word.
  Both Cargo configurations, with and without `mprotect`, run these tests; user-mode and
  mprotect semantics remain outside their scope. Exact cases and counts live in the
  [coverage table](../rust/sp1-comparison/README.md).
- ADD also has an exact algebraic comparison over arbitrary supervisor rows with untrusted
  programs disabled: upstream symbolic degree
  bounds justify a complete interpolation grid, and affine interaction occurrences match
  individually before permutation. Both AIRs must independently enforce the zero-register
  equation used in normalization. This is a trusted Rust check, not a kernel-checked theorem.
- All six native byte providers export without legacy lookups. AND/OR/XOR share a bundled
  bit-decomposition gadget in `ToClean`; the other providers use the same upstream bit primitives.
  Rust compares all byte pairs and four field multiplicities against SP1's actual preprocessed
  table and AIR, retaining every message occurrence. Native polynomial membership and SP1's
  authenticated preprocessing have different row layouts.
- All 17 installed Range providers compare with every released preprocessed row and AIR at four
  multiplicities, retaining duplicate zero-width rows. Both bump components compare with SP1's
  live trace generators, local constraints and complete ledgers, including timestamp/PC carries,
  padding and mutations of every column. Bump rows are supplied as inputs; this does not establish
  native execution-to-row generation or whole-ensemble balance.
- The syscall instruction, full-code guard and installed host-call wrapper export through Clean.
  Rust compares released supervisor rows, shared buses and public-value bindings, including all
  eight native codes, every commit slot and WRITE's extra register read. The public adapter uses
  named SP1 fields; `mprotect`'s additional supervisor trap cell must be zero before projection.
  A regression records unresolved padding drift: an inactive commit with an empty bitmap selects
  zero upstream but native addressed queries select previous-digest cells. Arbitrary-row public
  equivalence remains open under #29.
- HALT, constrained-replay ENTER, all sixteen commitment handlers and both bank terminals export
  with Lean row/ledger references. Rust executes real programs through SP1's executor and shard
  builder, then checks native effects, complete receipts and released Byte-table membership.
  Native commitment receipts describe each update to a mutable bank; SP1's syscall AIR binds
  each update to the shard's final public digest. Repeated differing writes execute with the
  same final bank but fail that upstream AIR condition. Both behaviors are tested explicitly;
  handler-effect agreement does not establish whole-shard AIR equivalence.
- Empty/nonempty HINT_LEN and HINT_READ handlers compare queue updates and word endpoints with
  released execution, including repeated observations, empty hints, mandatory final padding and
  limb carries. Complete active-host assembly must still authenticate all physical Memory writes
  and close the node, word and cursor ledgers.
- Source and target register authentication export their production sparse Memory provider and
  final-receipt consumer with separate fixed membership channels. Rust independently reconstructs
  register values and complete ledgers, including receipt clocks, and tests public binding and
  row/count mutations. Unused-provider cases retain all 32 fixed rows and zero-count occurrences.
  Arbitrary local snapshots are distinct from SP1's boot-only initialization. Generation alone
  does not establish acceptance: malformed address limbs can balance while violating assertions.
- Source and target RAM use the same fixed membership provider for normalized byte intervals.
  Byte/word reads and source/target row programs export through Clean. Independent Rust checks
  cover sparse gaps, first-entry precedence, address bounds, generated rows and complete ledgers.
  Closed interval-provider ensembles test fixed endpoints/bytes, counts, padding and public binding.
  General ordered RAM/host assembly generation and SP1 global-memory comparison remain open.
- Native write permissions authenticate writable intervals through a separate verifier-fixed
  provider. Requests carry only an address; the circuit selects interval witnesses internally
  using the same Clean IR selector as memory reads. The closed two-request export uses Clean's
  ordinary demand scheduler without private inputs. Rust checks literal ROM-byte exclusion,
  full rows/ledgers, public binding and interval/count mutations. Padding active permission
  tables at arbitrary request counts remains open. This is not SP1 runtime `mprotect`.
- Immutable hint nodes and words publish directly on their existing semantic channels from
  verifier-fixed payloads and eligibility tags. Rust reconstructs node/tail identities, lengths
  and little-endian words from literal byte buffers, including empty and aligned padding. Closed
  fixtures compare generation outcomes and all rows/ledgers, and test public/count/height binding.
  Native resource limits preserve the full word inventory; oversized inputs fail closed without
  truncation. This source-queue contract is separate from complete host execution.
- Static membership retains original row order and uses a fixed eligibility tag to select the
  first copy of a repeated payload. Duplicate and padding rows must have zero counts. Empty inventories
  have one inactive row; other heights round up to a power of two. Capacity proofs must account
  for this expansion. Clean's scheduler, lowering and emitter handle the resulting tables.
- The [independent backend fixtures](../tools/backend-gadgets/README.md) compile IsZero,
  IsZeroWord and WordRangeCheck through Clean's Circom/WASM/R1CS backend. Their positive,
  alternate-valid and rejecting cases test a separate backend boundary.

Reproduce current export checks after the full build:

```sh
python3 scripts/check_ensemble_export.py
scripts/check_backend_gadgets.sh
```

The R1CS path rejects lookups/interactions. A fixed lookup alone does not make a circuit R1CS
exportable. See [examples](examples.md) for the verified LoadByte replacement's narrower claim.

Rust comparisons use released SP1 code directly. The former reverse extractor, custom JSON
wire format, interpreter and committed dumps are retired. Native semantic proofs and reusable
mathematics remain; historical exact-AIR evidence is available in Git history.

## Rust migration

[#28](https://github.com/dtumad/sp1-lean/issues/28) owns the export boundary and executable
construction; [#29](https://github.com/dtumad/sp1-lean/issues/29) owns Rust comparison and
verified replacements. The final mixed compiler depends on #12, but current-ensemble export
and comparison can proceed first.

The compatible Clean pin supplies the built-in extraction IR, Rust emitter, fixed columns and
runtime prover inputs developed in upstream [#445](https://github.com/Verified-zkEVM/clean/pull/445)
and [#446](https://github.com/Verified-zkEVM/clean/pull/446). Cargo's backend revision is checked
against the Lean emitter pin. Generated Rust and reference rows live in the ignored build tree,
not in the library source. Additive gaps belong in ToClean; canonical upstream representation
changes may justify a minimal temporary dependency patch.

The fixed-membership fixtures establish native backend boundaries. Component comparisons keep
external buses open and check that an isolated active component cannot claim balanced execution.
The installed 94-component host assembly is lookup-free. Its branch and empty-segment exports
check complete assembly construction and Rust agreement for those cases. Broader execution
and host-call cases, general padding, data agreement and completeness remain open. The retired
instruction-only pipeline did not supply that missing whole-assembly coverage.

The native eight-call syscall profile uses degree-three arithmetic assertions and six shared
products. Its full-register contract remains independent of channel balance. Clean exports the
production guard and its witness program; Rust checks the selected codes against SP1’s pinned
enum, rejects upper-limb aliases and unselected calls, and checks generated rows and tampered
products. This profile is deliberately stricter than the executor’s truncating syscall dispatch.

The Clean patch supports message-filtered demand handlers and checked indexing into preallocated
providers. Production keeps SP1's specialized Byte providers: the channel payload selects the
opcode/width handler. Filters must identify one handler; ambiguous or missing matches are errors.
Indexed routes verify the selected row's actual message before changing its multiplicity.
Zero contributions do not enter the scheduler's pending-demand worklist; physical rows and their
zero-count ledger occurrences remain intact. These changes, plus the public-only-channel verifier
fix, modify existing upstream declarations and therefore live in the dependency patch. Remove each
patch when upstream provides the corresponding capability.

The same dependency patch lets `minimumRows := 0` preserve empty mutable tables. The Rust
backend keeps all indexed heights and widths, proving only nonempty tables; verifier-fixed
tables cannot be omitted. Verifier interactions and the complete occurrence bound still apply.
At least one table must be nonempty for the batch PCS. This removes spurious padding demands
from unused chips, but active tables still need valid padding to power-of-two heights.

Production retains the specialized Byte/Range providers. The archived
[provider review](https://github.com/dtumad/sp1-lean/pull/153) compares generation, proving,
verification, trace size and memory across small instruction cases and large workloads.
The unified alternative cost more on large distinct demand; fully preprocessed tables added
substantial proving and verification costs. Source and measurements remain in the linked checkpoints. Routine validation
covers the installed providers. Revisit this choice when upstream demand indexing or reusable
preprocessing changes those costs.

The existing test adapter constructs component rows with Clean's
runtime, then independently checks their external interactions. It is not a production scheduler
or evidence of full-ensemble balance. Rust tests establish neither cryptographic security nor a
formal lowering theorem.

The installed Program provider has sixteen verifier-fixed instruction fields and one prover-owned
count. It retains the complete decoded ROM, including unused entries, and pads with copies of the
first instruction. Empty inventories have an inert zero-count row. Physical table invariants and
Program balance authenticate counted fetches. Rust tests compare contiguous preprocessing and AIR
with SP1; separate tests cover the native model's sparse, unordered addresses. The additive
`ToClean.Air.MessageIndex` helper expresses first-match routing in Clean's existing witness IR;
its scheduler rechecks the complete payload. A scalable sparse index remains an upstream optimization.

The reviewed upgrade target is [SP1 v6.9.0](https://github.com/succinctlabs/sp1/releases/tag/v6.9.0).
The native row budget and canonical syscall-code restriction live in `Model/Core/Profile`,
independently of extraction. Cargo and the reviewed coverage record must agree with the release
revision in provenance.json. This is the only supported SP1 pin; old generated evidence is
historical rather than a second dependency.
Review loader byte preservation, host output behavior, instruction execution, verifier behavior
and table layouts separately; an unchanged instruction AIR does not imply unchanged system semantics.

Native `ProgramImage` consumes decoded instructions and byte memory; ELF parsing is an external
boundary. Guest public-output bytes are separate from the executor's bounded stdout/stderr display
snapshots. `HINT_READ` always writes a final padded word, including for zero or word-aligned lengths;
ordinary memory-initialization events do not add an empty word. The released executor regressions
in `rust/sp1-comparison/tests/release_semantics.rs` check these byte boundaries and instruction
execution behavior. They do not prove translation from ELF or executor equivalence.

The migration must cover:

1. ADD, memory and DivRem pilots; fixed lookups, prover data/hints, the public verifier and sharing.
2. All supported instruction families and the complete installed native physical inventory.
3. Valid and malformed native/SP1 witnesses, tables, interactions, public values, padding and
   count bounds, with deterministic generation and locked Cargo checks in CI.
4. Explicit failures for unsupported layouts, native-only witness programs and legacy lookup forms.
5. Native-owned carrier types and semantic proofs, with independent Rust comparison adapters.

Clean's witness scheduler is not a proof of totality, final-data agreement or completeness.
Retain constructor correctness and distinguish computable code from noncomputable semantic replay.
A function being data-only does not by itself establish that it can be exported.

## Coverage and mprotect

The [coverage record](../rust/sp1-comparison/inventory/coverage.json) accounts for both released
configurations and the complete installed native inventory: tables/widths, export support,
comparison evidence, semantic proofs and deliberate differences. The audit checks actual Lean
components; Cargo separately checks the Rust snapshots against source. Native ROM/host strengthening
requires a restricted comparison domain, recorded with each group's limits.

Rust's mode-associated columns include zero-width supervisor fields and populated user/mprotect
fields. Both configurations have independently checked inventories, but compiling the same
supervisor tests under both features does not establish user/mprotect execution coverage.

Represent statically optional columns as a configuration-indexed fixed-width/zero-width carrier.
ProvableType requires an exact vector isomorphism: ordinary runtime Option is not automatically
such a carrier. Runtime optional values need an explicit tag/payload validity contract or an
appropriate CircuitType. Solving representation does not prove mprotect semantics.

Rust comparison, formally verified lowering and cryptographic soundness remain distinct
assurance claims. Retiring the old pipeline does not close the outstanding native assembly or
capstone obligations.
