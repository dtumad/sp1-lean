# Semantics and scope

The durable target is soundness and constructive completeness of native Clean AIR for **bounded
local execution segments**, with complete source and target states and all eight constrained
host calls. A segment may continue, halt, or be empty; boot-to-HALT is a corollary.

```text
nativeEnsemble(context, commitments, source, target).Statement(canonicalHeader)
  ↔ ∃ events, StatementExecution(context, commitments, source, target, events)
```

This is a target, not an instantiated theorem. Its checked definitions are
[Shard.StatementExecution](../SP1Clean/FormalModel/Shard.lean) and the
[soundness/compiler targets](../SP1Clean/Soundness/Shard/Contract.lean).
[#12](https://github.com/dtumad/sp1-lean/issues/12) owns their remaining obligations.

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
| Construction builders | Chronological event/execution compilers, provider closure and capacity builders exist as C9/C10 starting material; they carry local success predicates and no completeness theorem over the fixed domain yet |
| Installed host assembly | Raw acceptance derives a valid source, the public clock, PC and execution flag, and a PolyFun trace covering all 25 ordinary families and the six installed syscalls. Both digests, both flags and each actual declaration agree with the verifier-owned commitment statement. [Trace theorem](../SP1Clean/Soundness/Shard/Trace.lean) |
| Outgoing host and clock | The production verifier decodes the ordered target hint suffix in the immutable incoming queue and checks the preserved host fields. The recovered trace reaches the supplied host and clock within the elapsed-tick budget. Every prefix respects the incoming limits on hint count, hint bytes, requests and output bytes. The assembler still takes the last hint-access timestamp as instance data. [Installed assembly](../SP1Clean/Export/InstalledAssembly.lean) |
| Complete Memory boundary | Installed target values and untouched-location coverage imply the finite comparison, and the accepted execution ends with exactly the supplied integer registers and RAM; the complete Memory ensemble retains its separate public verifier |
| Sail boundary | Equal incoming and outgoing clocks authenticate the complete realized target. For positive-duration segments the verifier fixes the invariant frame, retirement mode and observation endpoints. Recovering the exact target's dynamic bookkeeping from the combined physical ledgers remains open. |
| Constructive observation history | Routing supplies a chronological raw receipt for each ordinary instruction. The history constructs its counter update and ordered links, including raw clock carries. Guarded consumer rows retain zero-weight padding. A nine-instruction witness occupies sixteen observation rows and one terminal. [History construction](../SP1Clean/Proofs/Completeness/OrdinaryObservationHistory.lean) |
| Concrete examples | Accepted ADD and compiler-derived BEQ assemblies; LoadByte fixed-table replacement with occurrence-preserving transport |
| Released SP1 agreement | Direct Rust comparisons of exported native components; public-addressing and complete active-host assembly gaps remain explicit |

Current Rust evidence is tied to the single released-SP1 revision in
[provenance](../scripts/provenance.json). A release upgrade must review loader/host behavior as
well as AIR equations; it cannot be achieved by changing a version string.

The full mixed target equality, private terminal cursor/facade, fresh allocation authentication,
WRITE/VERIFY installation, complete resource enforcement, compatible capacity and total mixed
compiler remain open. No caller-supplied grounding, provider validity, syscall inactivity or
compiler-success premise may replace those obligations.

## Separate long-term claims

The native proof establishes AIR-to-execution meaning. Rust differential comparison establishes
tested agreement for a declared profile; formal code-generation correctness is another theorem.

A future SP1 verifier program has three layers: executable Core verifier agreement, cryptographic
knowledge soundness yielding an AIR witness with an error bound, and AIR-to-Sail refinement.
Core, Compressed, Plonk and Groth16 are distinct targets. An unconditional deterministic
`verifyCore = true → execution` theorem is not the intended cryptographic claim.
