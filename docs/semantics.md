# Semantics and scope

The durable target is soundness and constructive completeness of native Clean AIR for **bounded
local execution segments**, with complete source and target states and all eight constrained
host calls. A segment may continue, halt, or be empty; boot-to-HALT is a corollary.

```text
nativeEnsemble(context, commitments, source, target).Statement(canonicalHeader)
  ↔ ∃ events, ReleaseStatementExecution(context, commitments, source, target, events)
```

The equivalence is checked conditional on supplying both the soundness proof and a constructive
compiler. Its statement includes the broad resource-bounded Sail execution, commitment declarations,
and the link writes representable by the pinned release. [Release statement](../SP1Clean/FormalModel/ShardRelease.lean) · [Soundness and compiler targets](../SP1Clean/Soundness/Shard/Contract.lean) · [Remaining obligations](https://github.com/dtumad/sp1-lean/issues/12)

## State and execution

[Core execution](../SP1Clean/Semantics/Execution/Execution.lean) relates complete Sail state, concrete
host state and clock. [ExecutionPath](../SP1Clean/Semantics/Execution/ExecutionPath.lean) composes those
steps; finite [snapshots](../SP1Clean/Semantics/Execution/ExecutionSnapshot.lean) describe their boundaries.
Memory snapshots are projections, not an alternative execution model. Complete comparison
includes register-map presence, sparse RAM, simulator runtime, nextPC/retirement bookkeeping,
host queues, outputs, commitment banks, requests/replies and optional exit.

Ordinary steps execute the official Sail interpreter. Host calls use one evolving concrete
host/clock at a committed ECALL word. Committed code is the one fetch source of both arms; ROM
preservation proves that the executed word is also in Sail memory.
ENTER, HALT, COMMIT, COMMIT_DEFERRED, HINT_LEN, HINT_READ, WRITE and VERIFY belong to the
semantic domain.

Semantic events, elapsed ticks and physical AIR rows are different quantities. Ordinary
instructions cost eight ticks and host scheduling uses the explicit 264-tick window.
Refreshes and padding are implementation rows, not extra semantic instructions. An empty
identity preserves incoming observations, including optional nextPC and the increment flag.
A stopped source permits only an identity.

## Platform policy

The supported native profile is RV64 integer/multiply-divide execution on SP1's configured
platform. Unsupported instructions, compressed ISA/alignment mode, floating point, other
privilege profiles, user/mprotect AIR and cryptographic precompiles are not silently covered.

- Source validation supplies initialized architectural state and the generated SP1 platform
  configuration. The Sail model disables unsupported devices through generation-time settings;
  MPRV, pointer masking, relevant extension state and PMP/platform hypotheses remain explicit.
- Compressed alignment mode is excluded by `misa.C = 0`, not just by refusing compressed words.
- Committed code is readable from official Sail memory at each executed PC. A final PC need not
  be fetchable unless another step executes.
- Ordinary writes cannot touch protected code bytes, including same-value writes. Permission
  uses the decoded SB/SH/SW/SD byte span, not the enclosing eight-byte memory cell.
- Sail can normally retire misaligned accesses on this platform. Any narrower native AIR
  alignment restriction must appear in the semantic profile or be proved by its adapter;
  retirement alone is insufficient.
- Register x0, aliases, partial-cell writes and absent sparse keys retain their semantic meaning.
  Presence of a zero-valued register can matter at a complete boundary.

These are model choices and explicit compatibility boundaries. They must not be confused with
temporary missing proofs or with exact equality to upstream SP1's AIR.

## Resources and host effects

The concrete domain uses data-only `ResourceLimits` and `nativeProfile` computed from the existing
execution path. Limits describe semantic work, intermediate occupancy, encoding ranges and
boundary sizes. AIR soundness must derive them, and completeness must prove the full physical
construction fits them. Independent per-table or per-channel `p - 1` ceilings do not establish
a bound on their combined expansion. A conservative estimate may justify numeric parameters;
it must not become a per-execution readiness condition in the public equivalence.

Host effects include padding writes, peak queue/output/request resources, ordered byte streams
and fresh allocation history. Popping a hint does not authorize reusing its node.
WRITE must distinguish exact 64-bit descriptor branches from low32 branches and authenticate
x12, buffer reads, output, hints and hook replies. In both SP1 v6.9.0 and v6.10.0, VERIFY
ignores its pointers and preserves memory and host state. The return-register write, PC advance
and clock advance still occur. The earlier native verification-request model diverged from
v6.9.0 already. See the v6.9.0 [minimal dispatcher](https://github.com/succinctlabs/sp1/blob/v6.9.0/crates/core/executor/src/minimal/ecall.rs#L186)
and [replay dispatcher](https://github.com/succinctlabs/sp1/blob/v6.9.0/crates/core/executor/src/vm/syscall.rs#L404-L410).

The proof statement includes one immutable public-output digest, one deferred-proof digest and
their rolling flags. Every actual COMMIT or COMMIT_DEFERRED declaration must match its selected
word and a set flag. Public-output words are u32s. A deferred operand must be below the field
modulus. This matches the released syscall AIR. The minimal executor ignores the deferred
declaration, while constrained replay records the low 32 bits and sets the deferred flag.
A successful replay can therefore contain a declaration that fails the AIR's range check.
See the pinned [replay handler](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/vm/syscall/deferred.rs)
and [AIR check](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/machine/src/syscall/instructions/air.rs#L215-L222).

The operational host still records mutable banks: conflicting writes can execute, but cannot
satisfy one proof statement. Repeating an identical declaration is allowed. Partial and empty
segments need not cover every slot, and a set flag does not prove that any call occurred.
Consequently an incomplete mutable bank is not automatically equal to the full immutable digest.
Adjacent segments use the same statement; cutting a segment preserves declaration agreement.

## What is currently proved

| Surface | Result and limit |
|---|---|
| 25 instruction chips | Native soundness/completeness and Sail bridges; exported rows have separate released-Rust comparison tests |
| Execution model | Complete steps/paths, finite boundaries, split/join, semantic boot/HALT, independent ROM/frame/fetch preservation and PolyFun connections |
| Construction builders | Every admissible mixed execution determines one routed row per ordinary occurrence at its actual source PC and clock. The observation consumer has valid constraints and balanced receipt and state ledgers at the demand-mode height. Host and mixed Memory tables still need a joint construction. [Observation completeness](../SP1Clean/Proofs/Completeness/ExecutionObservation.lean) |
| Installed host assembly | Raw acceptance derives a valid source, the public clock, PC and execution flag, and a PolyFun trace covering all 25 ordinary families and the seven installed syscalls. Both digests, both flags and each actual declaration agree with the verifier-owned commitment statement. [Trace theorem](../SP1Clean/Soundness/Shard/Trace.lean) |
| Outgoing host and clock | The production verifier decodes the ordered target hint suffix in the immutable incoming queue and checks the preserved host fields. The recovered trace reaches the supplied host and clock within the elapsed-tick budget. Every prefix respects the incoming limits on hint count, hint bytes, requests and output bytes. A single fixed terminal row binds the public queue head and allocation frontier to a private 48-bit timestamp. The witness generator recovers that timestamp from the physical HINT_LEN and HINT_READ responses, with zero for an untouched queue. [Installed assembly](../SP1Clean/Export/InstalledAssembly.lean) |
| Complete Memory boundary | Installed target values and untouched-location coverage imply the finite comparison, and the accepted execution ends with exactly the supplied integer registers and RAM; the complete Memory ensemble retains its separate public verifier |
| Sail boundary | For arbitrary accepted seven-handler segments, the actual CPU order and physical receipt/terminal ledgers determine the last ordinary successor and the retirement count. The resulting nextPC, counter, increment flag, interrupt refresh and written event index identify the literal complete target. Adjacent accepted segments compose across extensionally equal boundaries. [Production soundness theorem](../SP1Clean/Export/InstalledAssembly.lean) |
| Constructive observation history | Routing supplies a chronological raw receipt for each ordinary instruction. The history constructs its counter update and ordered links, including raw clock carries. Guarded consumer rows retain zero-weight padding. A nine-instruction witness occupies sixteen observation rows and one terminal. [History construction](../SP1Clean/Proofs/Completeness/OrdinaryObservationHistory.lean) |
| Constructive observation endpoint | Every admissible mixed tape yields the demand-padded consumer, one selected terminal row and two empty terminal tables. Their signed ledgers balance against the actual routed receipts and the verifier’s source and target. The construction covers empty tapes, host suffixes, all 25 ordinary families and 64-bit retirement wraparound. [Four-table witness](../SP1Clean/Proofs/Completeness/ExecutionObservationEndpoint.lean) |
| Concrete examples | Accepted ADD and compiler-derived BEQ assemblies; LoadByte fixed-table replacement with occurrence-preserving transport |
| Composed execution | Any finite sequence of accepted seven-handler shards with agreeing complete boundaries yields a single trace with one commitment statement. From canonical boot to a stopped host, its final HALT carries the supplied exit code. [Shard composition](../SP1Clean/Export/ShardChain.lean) |
| Released SP1 agreement | Direct Rust comparisons of exported native components; public-addressing and complete active-host assembly gaps remain explicit |

The observation constructor is noncomputable in Lean. It replays the semantic path and uses the
typed instruction-event compiler to construct the witness. Clean’s executable ensemble scheduler
has a separate witness-generation contract. The four observation components retain their
constraints, guarantees and exact channel ledgers when Clean installs the canonical data of a
larger inventory. For a demand-padded consumer of height h, its receipt ledger has h occurrences
and the complete observation-state ledger has 2h + 4, including both public endpoints and the
selected terminal. This fits the standard native limits. [Canonical data](../SP1Clean/Proofs/Completeness/ObservationData.lean) and [physical capacity](../SP1Clean/Proofs/Completeness/ObservationCapacity.lean).

The broader `AdmissibleExecution` admits `jal x1,0` and `jalr x1,x0,0` from a checked
one-word boot image at the last instruction slot, `2^48 − 4`. Each writes `2^48` to x1. The
pinned JAL and JALR AIRs constrain an enabled link to three 16-bit limbs, so these same
complete source, target and tape triples fall outside `ReleaseAdmissibleExecution`. Raw acceptance of the installed
seven-handler assembly proves this link bound at every ordinary cut. The physical instruction
family, Program row and configured Sail decode identify the jump and destination register at
the replayed source PC.
Writing x0 disables the addition, and an enabled write from `2^48 − 8` still fits. Host calls
and empty paths have no link writes. The existing branch check uses the selected destination.
[Replay condition](../SP1Clean/Semantics/Execution/ReleaseLinks.lean) · [Physical row proofs](../SP1Clean/Proofs/Chips/JumpLinkBound.lean) · [Boot regressions](../SP1CleanTest/Alignment/Core/JumpLinkBoundary.lean)

Current Rust evidence is tied to the single released-SP1 revision in
[provenance](../scripts/provenance.json). A release upgrade must review loader/host behavior as
well as AIR equations; it cannot be achieved by changing a version string.

Fresh hint allocation authentication, WRITE installation, complete resource enforcement,
joint physical capacity and a total mixed compiler remain open. The seven-handler soundness theorem
already identifies the complete supplied target and recovers its private hint cursor from the witness. No caller-supplied grounding, provider validity, syscall inactivity or
compiler-success premise may replace those obligations.

## Separate long-term claims

The native proof establishes AIR-to-execution meaning. Rust differential comparison establishes
tested agreement for a declared profile; formal code-generation correctness is another theorem.

A future SP1 verifier program has three layers: executable Core verifier agreement, cryptographic
knowledge soundness yielding an AIR witness with an error bound, and AIR-to-Sail refinement.
Core, Compressed, Plonk and Groth16 are distinct targets. An unconditional deterministic
`verifyCore = true → execution` theorem is not the intended cryptographic claim.
