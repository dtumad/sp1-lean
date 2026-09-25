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

All `ResourceLimits` fields are inclusive ceilings. The `native` preset records encoding ceilings:
`2^24` elapsed ticks from pinned SP1 v6.4.0 `opts.rs`, `2^21` events, and `p-1` for the remaining
finite inventories. The preset does not assert that all ceilings can be saturated simultaneously;
construction must establish its complete expansion fits. It is not a theorem about the current
mixed AIR's accepted language. The exact-Core budget uses the same named tick constant.

| Quantity | Measurement | Enforcement / construction owner |
|---|---|---|
| events, ticks | Actual event tape and 8/264-tick durations | Ordered CPU occurrences and public clock boundary; execution scheduler |
| readBytes | Requested host read bytes, counting both logical VERIFY buffers | Bound host requests and byte observations; `HostFootprint`/`HostReadPlan` |
| writeBytes | Actual emitted host bytes, including mandatory HINT_READ padding | Word/write inventory and permission checks; hint word construction |
| allocatedHints | Cumulative fresh hints, including hook replies, independently of later pops | Fresh-node inventory; persistent queue construction |
| liveHints, liveHintBytes | Maximum actual queue occupancy over complete prefixes | Queue head/state binding; interpreter and queue representation |
| requests | Cumulative proof/hook observations | Request-bound host tables; host interpreter |
| outputBytes | Accumulated public/stdout/stderr bytes | Complete host boundary and WRITE observations |
| boundaryBytes | Canonical represented boundary data, not sparse update-history length | Complete source/target verifier; finite snapshot normalization |
| tableRows | Physical rows in each table, including providers/refresh/padding | Actual table inventory and all-table construction |
| channelOccurrences | Complete occurrence count in each registered channel | Clean ledger capacity and exact footprint accounting |

Numeric definitions do not close these rows. In particular the existing installed host inventory
omits WRITE/VERIFY, full target authentication remains open, and the legacy compiler accepts
ordinary executions only. These installation obligations belong to A4–A6. The resource work must
prove bounds for actual consumers and must not substitute a witness/readiness predicate for usage.

## Representation and retirement

The only complete execution model is `ExecutionPath` over Sail/host/clock, with paired replay and
`ExecutionSnapshot` boundaries. New resource records measure it; they do not carry a second path.
Usage must be invariant under equivalent snapshots. `MemorySnapshot` remains the provider view.
`HintQueue.Store` is a persistent implementation of semantic host queues, related by `Represents`.

| Compatibility surface | Replacement / removal condition |
|---|---|
| `EventExecutionTrace`, `CoreShardSemanticWitness` | Retain for ordinary/exact-Core consumers; migrate the mixed compiler to the complete path in A6. Delete only after retained exact/export consumers have adapters. |
| `InstructionPlanReady`, `NativeCompilerReady`, `NativeTraceReady` | Prove their applicable fields from semantics for retained APIs; no occurrence in the new domain. Remove wrappers once all relevant consumers use the derived results. The legacy `syscallFree` field cannot describe mixed execution. |
| `NativeTraceFootprint` | Migrate to shared accounting over every registered channel; retain an adapter while the ordinary compiler still consumes its named projections. |
| Explicit numeric range checks in older chip/Sail lemmas | Retain encoding-specific statements, derive their range facts from `NativeLayout`; factor more generally only with a migrated consumer. |

No whole-chip faithfulness anchor is retired by this work. Native range/resource strengthening
does not automatically become exact upstream SP1 refinement.
