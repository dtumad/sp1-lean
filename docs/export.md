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
- All 25 supported instruction families export through the same built-in path. Rust compares
  generated witnesses, local constraint satisfaction and complete
  interaction multisets with SP1 v6.8.1's supervisor AIR, including padding and column mutations.
  Multi-opcode components use explicit selectors without hints. Comparisons retain repeated and
  zero-multiplicity messages, including the multiplication gadget's caller-supplied result word.
  Both Cargo configurations, with and without `mprotect`, run these tests; user-mode and
  mprotect semantics remain outside their scope. Exact cases and counts live in the
  [coverage table](../rust/sp1-comparison/README.md).
- All six native byte providers export without legacy lookups. AND/OR/XOR share a bundled
  bit-decomposition gadget in `ToClean`; the other providers use the same upstream bit primitives.
  Rust compares all byte pairs and four field multiplicities against SP1's actual preprocessed
  table and AIR, retaining every message occurrence. Native polynomial membership and SP1's
  authenticated preprocessing have different row layouts.
- Source and target register authentication export their production sparse Memory provider and
  final-receipt consumer with separate fixed membership channels. Rust independently reconstructs
  register values and complete ledgers, including receipt clocks, and tests public binding and
  row/count mutations. Unused-provider cases retain all 32 fixed rows and zero-count occurrences.
  Arbitrary local snapshots are distinct from SP1's boot-only initialization. Generation alone
  does not establish acceptance: malformed address limbs can balance while violating assertions.
- Chip witness JSON and its Rust interpreter still compare against pinned SP1 dumps. They remain
  migration evidence while provider coverage and live consumers move to the built-in path.
- The [independent backend fixtures](../tools/backend-gadgets/README.md) compile IsZero,
  IsZeroWord and WordRangeCheck through Clean's Circom/WASM/R1CS backend. Their positive,
  alternate-valid and rejecting cases test a separate backend boundary.

Reproduce current export checks after the full build:

```sh
python3 scripts/check_witgen_export.py
scripts/check_ensemble_export.sh
scripts/check_backend_gadgets.sh
```

The R1CS path rejects lookups/interactions. A fixed lookup alone does not make a circuit R1CS
exportable. See [examples](examples.md) for the verified LoadByte replacement's narrower claim.

The transitional [JSON format](witgen-wire-format.md) has three artifacts per chip: witness
programs/constraints/interactions, a symbolic native-to-Rust row map, and a field/input/hint
manifest. The fixture exporter reconstructs actual SP1 trace rows before writing test data;
the [Rust interpreter](../rust/README.md) independently re-executes the serialized programs.
Native outputs live under `.lake/witgen-export/`; the driver checks two fresh exports for
byte agreement and runs locked Rust tests. Committed `export/sp1dump/` files remain independent
source inputs. `scripts/run_sp1_conformance.py` stages the pinned SP1 checker with fresh artifacts
under `.lake`, without modifying the extraction checkout. That opt-in check remains useful
migration evidence; it is not the intended long-term interpreter or dependency arrangement.

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

The fixed-membership fixture establishes the backend boundary. The instruction comparison keeps
external buses open and checks that each instruction alone cannot claim balanced execution. The native instruction/provider subset is lookup-free. The complete installed memory/host
inventory still contains legacy snapshot, program, permission and source-table lookups, which
built-in lowering rejects. Migrate those tables and all live consumers before retiring chip JSON
comparison. Rust tests do not establish
cryptographic security or a formal lowering theorem.

The reviewed upgrade target is [SP1 v6.8.1](https://github.com/succinctlabs/sp1/releases/tag/v6.8.1).
The active legacy evidence remains on the version in provenance.json until migration passes.
Review loader byte preservation, host output behavior, instruction execution, verifier behavior
and table layouts separately; an unchanged instruction AIR does not imply unchanged system semantics.

The migration must cover:

1. ADD, memory and DivRem pilots; fixed lookups, prover data/hints, the public verifier and sharing.
2. All supported instruction families and the complete installed native physical inventory.
3. Valid and malformed native/SP1 witnesses, tables, interactions, public values, padding and
   count bounds, with deterministic generation and locked Cargo checks in CI.
4. Explicit failures for unsupported layouts, native-only witness programs and legacy lookup forms.
5. Native-owned carrier types and migration of every old export/extraction consumer before deletion.

Clean's witness scheduler is not a proof of totality, final-data agreement or completeness.
Retain constructor correctness and distinguish computable code from noncomputable semantic replay.
A function being data-only does not by itself establish that it can be exported.

## Coverage and mprotect

The coverage record must compare the actual pinned Rust inventory independently of Lean's
registry, per configuration: tables/widths, witness support, tested comparison, semantic proof
and deliberate differences. Native ROM/host strengthening can require a restricted comparison
domain; label it.

Rust's mode-associated columns include zero-width supervisor fields and populated user/mprotect
fields. The legacy IntoShape extraction skips mode-dependent fields and explicitly rejects
mprotect. That gap is not proof coverage.

Represent statically optional columns as a configuration-indexed fixed-width/zero-width carrier.
ProvableType requires an exact vector isomorphism: ordinary runtime Option is not automatically
such a carrier. Runtime optional values need an explicit tag/payload validity contract or an
appropriate CircuitType. Solving representation does not prove mprotect semantics.

After coverage and consumers migrate, delete reverse extraction, faithfulness-only proofs, dumps,
the bespoke interpreter and duplicate export scripts. Preserve native semantic proofs and reusable
mathematics. Rust comparison, formally verified lowering and cryptographic soundness remain
distinct assurance claims.
