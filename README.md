<div align="center">

![SP1 Lean](./.github/assets/header.png)

Formal verification of SP1 Core instruction AIRs and native AIR-to-execution refinement

</div>

## Verified result

This repository verifies SP1's Core RISC-V instruction chips in Lean using the Clean circuit DSL
and the generated RISC-V Sail model. The SP1 semantic source is
`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529` (`v6.4.0`).

The main theorem is:

```lean
theorem supported_core_native_sound :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreSailRelation (p := p))
```

Its input has three parts: the native ensemble's constraints and channel balance; a semantic
binding for the program, providers, and initial Sail state; and `SyscallTableInactive`, requiring
an inactive syscall table and a physically present Halt table.

The conclusion is a shard-local execution of the official generated Sail interpreter: either a
normally retiring instruction sequence, or such a sequence followed by the modeled HALT handler.
The public PC and clock endpoints agree with the execution. Ordinary instructions take eight
ticks; HALT adds 264. Program loading, platform configuration, and code/memory compatibility are
explicit assumptions. The Memory timestamp bounds are derived in the grounding proof.

The native ensemble has **55 tables and seven channels**, plus its separate verifier row.
It contains 25 instruction tables and 30 provider/system tables, including Halt and SyscallInstrs.
Registering the full syscall chip does not make active syscall rows part of the current soundness
theorem.

## Coverage and limits

| Result | Current boundary |
|---|---|
| 25 instruction-chip soundness and completeness proofs | Native Clean circuits and their semantic contracts |
| 25 Sail instruction bridges | Supported RV64IM instruction routes |
| 25 whole-chip Rust faithfulness proofs | Complete assertion systems and active interaction multisets on reconstructed native rows |
| Full SyscallInstrs chip and factored faithfulness proof | Local row result with explicit public-value binding; active syscall grounding remains unfinished |
| Native AIR-to-Sail soundness | Explicit semantic boundary and inactive syscall table |
| Deterministic native completeness | All 25 instruction families on the named admissible, ordinary-shard domain |
| Single-shard boot-to-halt theorem | Requires a boot boundary and live Halt row; no joint inhabitant is constructed yet |
| Exact upstream Core AIR-to-Sail refinement | Conditional on an unconstructed obligations bundle |

The compiler builds instruction rows, State/Memory refreshes, Memory boundaries, and recounted
Byte/Range/Program providers. It currently emits a padding Halt row and an empty SyscallInstrs
table. Its source relation retains explicit readiness and interaction-capacity conditions.
Unconditional correctness and language equality for the ordinary sub-language still require
`NativeShardTraceTotal`. The active regression joins an official Sail step, its deterministic
compiler event, a nonempty bounded native witness, and native soundness back to Sail.

The complete extracted upstream relation contains the paired **34-table execution** and
**six-table memory-boundary** clusters and the **160-cell public-value block**. Its local transport
constructs the native ensemble under named contracts; its Halt and SyscallInstrs tables are
manufactured padding/empty tables, not a transport of upstream syscall events. Global balance,
authenticated preprocessing, semantic boundary binding, and syscall refinement remain explicit
obligations.

The exact-AIR declarations are therefore named
`sp1_air_refinement_of_obligations` and `sp1_air_sound_of_obligations`.
Neither a closed exact-Core soundness theorem nor cryptographic verifier soundness is claimed.
A future verifier theorem must account for cryptographic assumptions and an extraction error bound.
Cross-shard composition and completeness are separate results.

## Trust and dependencies

All dependencies are pinned in `lake-manifest.json`, with Lean/mathlib v4.32.2. The important
boundaries are:

- **SP1 extraction:** a pinned Rust compiler/exporter produces complete row shapes and
  assertion/interaction lists. Its tooling remains trusted; source-delta checks, whole-chip
  faithfulness proofs, and trace conformance provide separate evidence.
- **Clean:** the dependency is a pinned fork containing changes to prover-data agreement and
  witness-program sharing. Local additions live in `ToClean/`. The exact differences are
  disclosed in the [release audit](docs/release-audit.md).
- **Sail:** the generated model and runtime are pinned together. The model is regenerated with
  the checked-in SP1 platform configuration; loader and initial-state hypotheses remain explicit.
- **Lean:** main-library proofs have no proof deferrals, project axioms, kernel bypasses, or
  `native_decide`. Generated Sail platform hooks and selected bit-vector proof constants are
  disclosed in the [axiom ledger](docs/snapshots/axiom-ledger.md). Compiler-trusted executable
  tests live separately in `SP1CleanTest/`.

Do not run bare `lake update`; dependency changes require a reviewed pin change.

## Build and reproduce

```bash
lake build SP1Clean
lake test
lake lint
scripts/run_audit.sh
```

Trace conformance also uses `scripts/check_witgen_export.sh --regen` and
`scripts/run_interp_diff.sh`. Regenerating the Rust extraction requires a clean checkout of its
separate extraction pin; [the extraction procedure](docs/agents/extraction.md) documents it.
A successful cached build checks a different reproduction boundary from rebuilding the project
without its previous oleans.

## Review and contribute

For the consolidated eight-PR development, start with the
[capstone assessment](docs/audits/2026-09-capstone-assessment.md), which records reproduction,
confirmed defects, and remaining proof obligations. For the implementation, read the
[verification overview](docs/overview.md), then the
[technical report](docs/verification-report.md), [semantic audit surface](docs/audit-surface.md),
and [architecture](docs/architecture.md). The [documentation index](docs/README.md) identifies
each document's role. Remaining work is described in the [roadmap](docs/roadmap.md).

The main source layers are `Math`, `Model`, `Extracted`, `FormalModel`, `Native`, `Proofs`,
`Faithful`, `Composition`, and `Soundness`. Extraction produces Lean data, not Clean circuits;
the native circuits are maintained independently. The whole chip is the Rust-faithfulness boundary.

[AGENTS.md](AGENTS.md) records contributor rules. Clean's pinned proof and performance documentation
is authoritative for circuit proofs; the [local proof notes](docs/agents/proof-patterns.md)
describe SP1-specific applications.

## License

Dual-licensed under either [Apache License 2.0](LICENSE-APACHE) or [MIT](LICENSE-MIT), at your
option. Unless explicitly stated otherwise, contributions are dual-licensed under the same terms.
