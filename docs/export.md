# Export and integration

Lean owns native circuits, their Specs and their correctness proofs. The target integration is:

```text
Lean semantics → proved Clean circuits/witnesses → Clean Rust export → Rust/SP1 comparison
```

Use Clean's existing AIR extraction IR, lowering, Rust emitter and Witgen IR. Keep only thin
SP1 field/trait/event/layout/channel adapters. Do not grow another emitter, wire format,
interpreter or scheduler.

## Current facilities

- Circuit witnesses use exportable Clean IR, with a proved sharing pass in ToClean to avoid
  duplicating large expressions.
- ToClean's finite checker authenticates fixed lookup inventories and
  connects executable checks to raw Clean assertions and channel balance, including the public
  verifier and occurrence capacity.
- The whole-ensemble fixture uses Clean's built-in Rust exporter and backend. Verifier-fixed
  columns replace its legacy lookup; fresh Rust witnesses are compared with Lean reference rows,
  and backend proofs exercise public binding, row constraints and rejected mutations.
- Chip witness JSON and its Rust interpreter still compare against pinned SP1 dumps. They are
  transitional evidence until instruction coverage moves to the built-in path.
- The [independent backend fixtures](../tools/backend-gadgets/README.md) compile IsZero,
  IsZeroWord and WordRangeCheck through Clean's Circom/WASM/R1CS backend. Their positive,
  alternate-valid and rejecting cases test a separate backend boundary.

Reproduce current export checks after the full build:

```sh
scripts/check_witgen_export.sh --regen
scripts/check_ensemble_export.sh
scripts/run_interp_diff.sh
scripts/check_backend_gadgets.sh
```

The R1CS path rejects lookups/interactions. A fixed lookup alone does not make a circuit R1CS
exportable. See [examples](examples.md) for the verified LoadByte replacement's narrower claim.

The transitional [JSON format](witgen-wire-format.md) has three artifacts per chip: witness
programs/constraints/interactions, a symbolic native-to-Rust row map, and a field/input/hint
manifest. The fixture exporter reconstructs actual SP1 trace rows before writing test data;
the [Rust interpreter](../rust/README.md) independently re-executes the serialized programs.
`scripts/run_sp1_conformance.sh` runs the comparison inside the pinned SP1 extraction checkout,
after checking its vendored artifacts against this repository. That opt-in check remains useful
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

The fixed-membership fixture establishes this backend boundary only. The complete native
inventory still contains legacy lookups, which built-in lowering rejects. Migrate those providers
and the remaining witness-sharing consumers before retiring chip JSON comparison. The new Rust
tests use test FRI parameters and do not establish cryptographic security or a formal lowering theorem.

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
