# Native resource contract

The concrete native facade uses data-only numeric limits. A limit is an explicit policy choice;
it is not evidence that the existing AIR enforces it or that every bounded execution compiles.
The capstone needs both directions against the same domain. Current implementation and PR status
belong to fork campaigns [#12](https://github.com/dtumad/sp1-lean/issues/12) and
[#16](https://github.com/dtumad/sp1-lean/issues/16).

## Ranges and representation

`AddressRange` owns lower/upper bounds, and `MemorySpan` owns requested byte intervals and their
eight-byte-cell cover. Byte membership is half-open. Span containment checks the full natural
sum before narrowing; an empty span may start at the upper endpoint, matching existing host
reads. It may not start below the lower bound or beyond the upper bound.

`NativeLayout.guestMemory = [2^16, 2^48)` is the SP1 PMA/guest-access instance.
`NativeLayout.sailMemory = [0, 2^48)` is the byte-key domain represented by a complete Sail
snapshot. These are distinct: an inaccessible byte can still be present in the memory map.
`HostMemoryPolicy.range` consumes the shared range; its `lower`/`upper` names are compatibility
projections, not additional stored bounds. Program-image checks use the same guest instance.
Other range values are meaningful for the generic arithmetic/host interface, not a claim that
arbitrary layouts have been proved against the fixed generated Sail model or SP1 chips.

The clock encoding has two 24-bit limbs. An active access must additionally fit its actual local
timestamp window. Source validity alone does not imply phase one modulo eight; that premise of
an older compiler helper must not become a silent domain restriction. Sail permits misaligned
ordinary data accesses. The specific alignment imposed by native chip encodings is a separate
representability condition, not a Sail fault assumption.

## Quantities and proof ownership

All `ResourceLimits` fields are inclusive ceilings. The `native` preset records count budgets:
`2^24` elapsed ticks from pinned SP1 v6.4.0 `opts.rs`, `2^21` events, and `p-1` for the remaining
finite inventories. The preset does not assert that all ceilings can be saturated simultaneously;
construction must establish its complete expansion fits. It is not a theorem about the current
mixed AIR's accepted language. In particular, `p-1` is a field-count ceiling, not a proof that
all pointer/length encodings fit for an arbitrarily large characteristic. Fixed bit-width bounds
and combined persistent-allocation bounds remain separate checks. The exact-Core budget uses
the same named tick constant.

| Quantity | Measurement | Enforcement / construction owner |
|---|---|---|
| events, ticks | Actual event tape and 8/264-tick durations | Ordered CPU occurrences and public clock boundary; execution scheduler |
| readBytes | Requested host read bytes, counting both logical VERIFY buffers | Bound host requests and byte observations; `HostFootprint`/`HostReadPlan` |
| writeBytes | Actual emitted host bytes, including mandatory HINT_READ padding | Word/write inventory and permission checks; hint word construction |
| allocatedHints | Cumulative fresh hints, including hook replies, independently of later pops | Fresh-node inventory; persistent queue construction |
| liveHints, liveHintBytes | Maximum actual queue occupancy over complete prefixes | Queue head/state binding; interpreter and queue representation |
| requests | Peak complete request-list length, including incoming observations | Request-bound host tables; host interpreter |
| outputBytes | Accumulated public/stdout/stderr bytes | Complete host boundary and WRITE observations |
| boundaryBytes | Live nonzero RAM plus length-prefixed host payload and Sail output strings, maximized over boundaries | Complete source/target verifier; finite snapshot normalization |
| tableRows | Physical rows in each table, including providers/refresh/padding | Actual table inventory and all-table construction |
| channelOccurrences | Complete occurrence count in each registered channel | Clean ledger capacity and exact footprint accounting |

Numeric definitions do not close these rows. In particular the existing installed host inventory
omits WRITE/VERIFY, full target authentication remains open, and the legacy compiler accepts
ordinary executions only. These installation obligations belong to A4–A6. The resource work must
prove bounds for actual consumers and must not substitute a witness/readiness predicate for usage.

## Installed endpoint checks and remaining enforcement

`Native/Operations/ResourceBoundary.lean` implements a real verifier subcircuit checking the
source and supplied target's finite occupancy, natural elapsed ticks, and target PC/clock range.
Its clock equations bind that target clock to the actual outgoing State token.
`Soundness/ResourceEnsemble.lean` installs it over the current source-hint assembly and derives
actual elapsed-work bounds from raw constraints and balance. Every event consumes at least
eight ticks; this proves the native preset's event ceiling, including 264-tick host calls.
It does **not** enforce an arbitrarily tighter independent `events` ceiling.

`ToClean/Air/PublicVerifier.lean` preserves the literal tables and all-channel interaction lists,
including order, repetitions and zero-multiplicity occurrences. The installed statement is proved
equivalent to the original raw statement plus the exact endpoint checks. The semantic domain
proves these checks for completeness; no conservative expansion estimate is imposed here.
Stopped identities retain their original clock and need no active-event phase.

The enforcement obligations remain explicit:

| Remaining conclusion | Owner / required evidence |
|---|---|
| Supplied target occupancy equals actual outgoing occupancy | A4 complete target authentication; clock equality alone is insufficient |
| Every intermediate live queue/RAM/output/request peak fits | A4/A5 constrained resource accounting at actual prefixes |
| Arbitrary independent event/read/write/allocation ceilings | A4/A5 exact occurrence/cost accounting, including padded writes and both VERIFY observations |
| Fixed pointer/length widths and cumulative persistent allocation | A5 queue/request installation; individual field-count ceilings are insufficient |
| Whole `ExecutionPath.Encoded` derived from registered rows | R4 adapter from existing chip contracts and actual prefix decoding |
| Physical height and every channel's occurrence ceiling | R5 inventory/capacity accounting; final A4/A5/A6 tables must be included when installed |

These are unproved implementation obligations, not additional capstone premises. The endpoint
checker regression deliberately accepts a boundary whose tape exceeds the padded-write budget:
it prevents an endpoint-only check from being mistaken for complete resource enforcement.

## Representation and retirement

The only complete execution model is `ExecutionPath` over Sail/host/clock, with paired replay and
`ExecutionSnapshot` boundaries. New resource records measure it; they do not carry a second path.
`ExecutionResources` observes the existing replay, summing events/ticks/read/write/allocation work
and taking maxima for live resources. It includes both sides of each real step; empty identities
check their incoming occupancy separately. `resources_append` and `resources_split` prove the
arithmetic at complete semantic cuts. `ExecutionSnapshot.resources_realize` computes occupancy
without materializing dense Sail memory; `ByteMemory.supportBelow` removes zeros and shadowed
writes. Both state and tape usage are invariant under equivalent complete snapshots.

`nativeProfile` is fixed at the Shard and PolyFun target consumers. It requires width-aligned
ordinary LOAD/STORE spans and the actual low-clock window (`clock % 2^24 + 4 < 2^24`), not phase
one modulo eight. Normal Sail retirement alone does not imply width alignment. Final PC/clock
fit their native encodings but need no subsequent fetch. The physical `tableRows` and
`channelOccurrences` ceilings still await the R5 capacity consumer; the semantic measurements do
not stand in for that proof. `boundaryBytes` is a variable-payload measure, not a full Sail
serialization-size theorem: fixed public register/platform data and the final boundary circuit's
actual row cost remain part of A4/R5. No bounded-ensemble instance is claimed by these definitions. `MemorySnapshot` remains the provider view.
`HintQueue.Store` is a persistent implementation of semantic host queues, related by `Represents`.

| Compatibility surface | Replacement / removal condition |
|---|---|
| `EventExecutionTrace`, `CoreShardSemanticWitness` | Retain for ordinary/exact-Core consumers; migrate the mixed compiler to the complete path in A6. Delete only after retained exact/export consumers have adapters. |
| `InstructionPlanReady`, `NativeCompilerReady`, `NativeTraceReady` | Prove their applicable fields from semantics for retained APIs; no occurrence in the new domain. Remove wrappers once all relevant consumers use the derived results. The legacy `syscallFree` field cannot describe mixed execution. |
| `NativeTraceFootprint` | Migrate to shared accounting over every registered channel; retain an adapter while the ordinary compiler still consumes its named projections. |
| Explicit numeric range checks in older chip/Sail lemmas | Retain encoding-specific statements, derive their range facts from `NativeLayout`; factor more generally only with a migrated consumer. |

No whole-chip faithfulness anchor is retired by this work. Native range/resource strengthening
does not automatically become exact upstream SP1 refinement.
