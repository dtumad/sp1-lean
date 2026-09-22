# Verification overview

This is a guide to the current theorem boundary. The [technical report](verification-report.md)
contains the detailed arguments; the [release audit](release-audit.md) records dependency pins and
trust boundaries. SP1 is pinned to `v6.4.0`, and Lean/mathlib to v4.33.1.

## Local shard capstone

The current mixed AIR derives a local path from a complete checked incoming Sail/host state,
with exact active-event coverage and final PC/clock/Memory-frontier agreement. Complete outgoing
state binding, WRITE/VERIFY with authenticated allocations, and full constructive completeness
remain open. The checked end-to-end targets reuse the existing execution path and generic Clean
interfaces; they are not completed instances. See [the roadmap](roadmap.md) for the compact status
and implementation order, and the [report](verification-report.md#72-full-state-local-shard-semantics-and-the-installed-mixed-air)
for the proof boundary.

## Coverage register

The first capstone targets the existing native ensemble and the supported decoder's normal
RV64 integer execution, with all eight selected host calls. It is not a claim about every RISC-V
instruction or every SP1 mode. The categories below are part of the review contract; proof gaps
must not be relabelled as intentional exclusions merely to close a theorem.

| Classification | Behavior and enforcement | Exit criterion / owner |
|---|---|---|
| Intentional profile exclusion | Dynamic SP1 `mprotect`, user-mode/trap tables, precompiles, and optional retention clusters are absent from `CoreProfile`; extraction checks that Cargo does not enable `mprotect`. | Separate profiles and whole-table refinement, outside the first capstone. Native immutable-ROM protection is a different mechanism. |
| Intentional ISA exclusion | `InstructionDecode.decode` selects the supported 32-bit integer/M encodings and ECALL. Compressed, atomic, floating/vector, privileged and trapping execution are outside this profile. | An explicit decoder/semantic/circuit extension; never infer full RV64IM coverage from the 25 chip families. |
| Platform and resource policy | Configured Sail machine mode, immutable checked ROM, aligned accesses, 48-bit native address/clock space, and finite field/host capacities. SP1's trusted/supervisor profile is not Sail Supervisor privilege. | State every bound in the concrete semantic profile and derive/check it in the AIR; capacities must not be defined by compiler success. |
| Temporary decoder limitation | Enabled Zicbop/Zihintntl encodings that overlap integer no-ops are rejected by `reservedHint`, because Sail selects distinct constructors. | Prove those constructors' bridges and extend the decoder/profile explicitly (campaign B). |
| Temporary SP1 compatibility restriction | Native syscall decoding requires canonical full 64-bit words. Rust dispatches on the low 32 bits; executor return normalization and AIR raw-word preservation need separate comparison. | A proved executor/AIR compatibility domain or a changed native syscall adapter, with alias regressions (campaign A's exact-refinement follow-up). |
| Deliberate execution observation | Commit banks are mutable, as in the Rust executor. Exact SyscallInstrs AIR compares every commit to a fixed public digest. | State the compatible trace/public-value domain in exact refinement; do not erase intermediate execution updates. |
| Explicit external boundary | ENTER models constrained replay and returns zero. Hook replies are request-bound input data; WRITE records bytes. VERIFY records an observed request, not cryptographic acceptance. | Authenticate all observations/effects in the native AIR. Verification of external proofs and unconstrained execution are separate claims. |
| Capstone-blocking proof debt | Free resource `Profile`, AIR derivation of the fixed ordinary-write policy and independent path ROM/fetch preservation, full supplied-target binding, WRITE/VERIFY and fresh allocation installation, and mixed compiler totality. | Close campaign A; none may become a caller premise or permanent syscall exclusion. |
| Separate refinement | Pinned SP1's complete AIR, preprocessing/PCS identity, succinct boundary commitments, and cryptographic verifier soundness. | Separate proved interfaces, assumptions and error bounds; native correctness does not imply these results. |

The code authorities are `Model/Core/{InstructionDecode,Execution,HostExecution,SyscallCode}`,
`Model/Core/SourceExecution`, `FormalModel/{Shard,CoreProfile}`, and `update_extracted.py`'s
`verify_no_mprotect`. [The roadmap](roadmap.md) owns progress; this table owns the meaning of each
restriction. Complete finite source/target snapshots are public instance data in the native
statement, even when only a bounded canonical header occupies the field-valued public input.

## Retained 55-table native soundness

`supported_core_native_sound`, in `SP1Clean/Soundness/AIR.lean`, proves:

```lean
WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
  (SupportedCoreSailRelation (p := p))
```

The input relation has three conjuncts:

| Premise | Meaning |
|---|---|
| `SupportedCoreEnsembleRelation` | The public input agrees with the statement, all table constraints hold, and every ensemble channel balances. |
| `SP1SemanticBoundaryRelation` | The program, providers, shared prover data, and a concrete initial Sail state agree under explicit loader, platform, and code-memory contracts. |
| `SyscallTableInactive` | The SyscallInstrs table has no active row and the Halt table contains a physical row. |

The semantic boundary supplies program well-formedness and commitment, the initial clock,
`ShardStartState`, `SailCodeMemoryCompatible`, and provider content and uniqueness facts.
It does not assume the execution trajectory that the proof constructs. The proof derives
pulled-Memory timestamp bounds from per-location balance.

The conclusion uses the official generated Sail interpreter, with normal retirement at every
ordinary step. It is either an ordinary sequence between the public endpoints or an ordinary
prefix reaching `SP1Halted`, followed by the modeled HALT handler. Ordinary steps take eight ticks;
HALT adds 264. The intermediate grounding theorem also retains agreement between the populated
Memory boundary and the initial/final states.

This is shard-local. The separate `supported_core_boot_to_halt_single_shard` theorem adds a boot
boundary and a live Halt row. Its joint input relation has no constructed inhabitant yet.
Neither theorem establishes cryptographic verifier acceptance or cross-shard composition.

## Physical machine and chip coverage

`sp1Ensemble` contains **55 tables**, plus its state-boundary verifier:

| Positions | Tables |
|---|---|
| 0–24 | The 25 supported instruction chips |
| 25–30 | Six Byte providers |
| 31–47 | Range providers for every width 0–16 |
| 48 | Program |
| 49–50 | MemoryInit and MemoryFinalize |
| 51–52 | MemoryBump and StateBump |
| 53 | Halt |
| 54 | SyscallInstrs |

Its seven channels are State, Byte, Program, Memory, Exit, Syscall, and PublicValues.
The retained 55-table relation makes the last two ledgers silent by requiring an inactive
SyscallInstrs table.

Every one of the 25 instruction families has native soundness and completeness, a Sail bridge,
and a whole-chip faithfulness proof against complete extracted Rust assertion and interaction
lists. The comparison reconstructs a canonical native physical row from an arbitrary extracted
row; it is not an equivalence over every possible native assignment.

The full SyscallInstrs circuit has a separate whole-row result:
`syscallInstrsChip_faithful` factors Rust's public-value assertions into an explicit
`PublicValueBinding` and native public-value messages. It does not prove that the ensemble
discharges that binding. The PublicValues provider and the connection from mixed-row grounding to
the event capstone remain unfinished.

The current Halt circuit is a restricted native model of one syscall arm. It requires a canonical
HALT register value and a 16-bit exit code. It is not the full SyscallInstrs row and has no
whole-chip Rust faithfulness anchor.

## Native completeness and non-vacuity

`supported_core_native_functionalCompleteness` constructs the entire native witness from an
admissible semantic shard. The deterministic compiler covers all 25 ordinary instruction families,
generates refreshes and Memory boundaries, and recounts Byte/Range/Program providers from its
actual interactions. It emits one padding Halt row and an empty SyscallInstrs table.

The admissible source retains `NativeTraceReady` and `NativeTraceFootprint.Fits`. These include
successful ordinary-event compilation, semantic and circuit-row agreement, provider servability,
zero exit code, and per-channel interaction capacity. They are visible conditions, not a proved
totality result on all bounded semantic executions.

Soundness and completeness share a bounded shard vocabulary. The
`supported_core_native_shard_correct_of_totality` and
`supported_core_native_shard_language_eq_of_totality` theorems concern its ordinary sub-language
and require the unproved `NativeShardTraceTotal` condition.

The executable regressions include both a zero-event admissible shard and an active join:
an official Sail self-jump, its deterministic compiler event, a nonempty bounded AIR witness, and
soundness back to the shared semantic language. These establish particular joint witnesses; they
do not establish universal compiler totality or boot-to-HALT non-vacuity.

## Exact upstream AIR boundary

The extracted relation pairs the 34-table execution cluster with the six-table memory-boundary
cluster and the 160-cell public-value block. Its natural send/receive balance is a knowledge-extracted
witness relation, not raw verifier acceptance.

The instruction transport uses all 25 faithfulness proofs. Under named local contracts, source-backed
preprocessing inventory, and public-boundary conditions, `Composition/` constructs all native
tables and proves their local constraints. Its Halt and SyscallInstrs tables are manufactured
padding/empty tables; upstream syscall events are not transported by that construction.

Remaining global inputs include interaction-count bounds, State/Memory/Exit integer balance,
authenticated preprocessing and program identity, and semantic boundary binding.
`CoreAIRRefinementObligations` also requires public-value well-formedness and shard transitions,
syscall transcript and COMMIT operand facts, Memory boundary agreement, and execution/boundary cases.
There is no closed construction of the bundle.

The public declarations are therefore `sp1_air_refinement_of_obligations` and
`sp1_air_sound_of_obligations`. A full exact-Core theorem additionally needs the supported syscall
profile and host semantics resolved. Full-word canonical syscall codes are an explicit restriction;
the Rust executor's `u32` dispatch alone does not establish it.

## Reproduction and review

Run `lake build SP1Clean`, `lake test`, `lake lint`, and `scripts/run_audit.sh`.
The [axiom ledger](snapshots/axiom-ledger.md) records the main/test split and disclosed dependency
classes. The main library contains no proof deferrals, project axioms, or `native_decide`.

Regenerating witness exports, SP1 trace dumps, and extracted AIR lists tests separate boundaries.
The Rust differential compares all committed fixture rows, while a fresh project build checks
independence from prior project oleans. None substitutes for reviewing the semantic contracts or
the trusted exporter.

Use the [audit surface](audit-surface.md) for definition-level review and the
[roadmap](roadmap.md) for the remaining constructions.
