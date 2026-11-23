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

The clock encoding has two 24-bit limbs. Every active native CPU row also has phase one modulo
eight: the shared `Native/Readers/CPUState.lean` circuit constrains `(clk_0_16 - 1) / 8` by a
13-bit range lookup. Ordinary instruction and host rows both use it. `TimeExtraction.cpuState_clock_phase`
derives the phase from that actual specification. Source validity and the broader Sail/host
execution relation do not imply it. The native profile therefore requires the phase explicitly;
empty/stopped identities do not. The generic scheduler needs only room for its four local offsets,
and its window lemmas retain phase-one compatibility wrappers. Sail permits misaligned
ordinary data accesses. The specific alignment imposed by native chip encodings is a separate
representability condition, not a Sail fault assumption.

## Quantities and proof ownership

All `ResourceLimits` fields are inclusive ceilings. The `native` preset records count budgets:
`2^24` elapsed ticks (`MAX_SHARD_SIZE` in pinned SP1 v6.10.0 `opts.rs`), `2^21` events, and `p-1`
for the remaining finite inventories. The preset does not assert that all ceilings can be saturated
simultaneously; construction must establish its complete expansion fits. It is not a theorem about
the current mixed AIR's accepted language. In particular, `p-1` is a field-count ceiling, not a
proof that all pointer/length encodings fit for an arbitrarily large characteristic. Fixed
bit-width bounds and combined persistent-allocation bounds remain separate checks. The tick
ceiling is the named constant `NativeLayout.maxShardTicks`.

| Quantity | Measurement | Enforcement / construction owner |
|---|---|---|
| events, ticks | Actual event tape and 8/264-tick durations | Ordered CPU occurrences and public clock boundary; execution scheduler |
| readBytes | Requested WRITE bytes; VERIFY reads none | Bound host requests and byte observations; `HostFootprint`/`MemorySpan` |
| writeBytes | Actual emitted host bytes, including mandatory HINT_READ padding | Word/write inventory and permission checks; hint word construction |
| allocatedHints | Cumulative fresh hints, including hook replies, independently of later pops | Fresh-node inventory; persistent queue construction |
| liveHints, liveHintBytes | Maximum actual queue occupancy over complete prefixes | Queue head/state binding; interpreter and queue representation |
| requests | Peak complete request-list length, including incoming observations | Request-bound host tables; host interpreter |
| outputBytes | Accumulated public/stdout/stderr bytes | Complete host boundary and WRITE observations |
| boundaryBytes | Live nonzero RAM plus length-prefixed host payload and Sail output strings, maximized over boundaries | Complete source/target verifier; finite snapshot normalization |
| tableRows | Physical rows in each table, including providers/refresh/padding | Actual table inventory and all-table construction |
| channelOccurrences | Complete occurrence count in each registered channel | Clean ledger capacity and exact footprint accounting |

Numeric definitions do not close these rows. In particular the existing installed host inventory
covers every supported call except WRITE. Constructing the full mixed witness and proving its capacity remain open. These installation obligations belong to A4–A6. The resource work must
prove bounds for actual consumers and must not substitute a witness/readiness predicate for usage.

## Installed endpoint checks and remaining enforcement

`Native/Operations/ResourceBoundary.lean` implements a real verifier subcircuit checking the
source and supplied target's finite occupancy, natural elapsed ticks, and target PC/clock range.
Its clock equations bind that target clock to the actual outgoing State token.
`Soundness/ResourceEnsemble.lean` installs it over the current source-hint assembly and derives
actual elapsed-work bounds from raw constraints and balance. Every event consumes at least
eight ticks; this proves the native preset's event ceiling, including 264-tick host calls.
It does **not** enforce an arbitrarily tighter independent `events` ceiling.

`ToClean/Air/PublicVerifier.lean` preserves the literal tables and every existing channel ledger,
including order, repetitions and zero-multiplicity occurrences. Its fresh assertion channel
accounts for the endpoint checks. The installed statement is proved
equivalent to the original raw statement plus the exact endpoint checks. The semantic domain
proves these checks for completeness; no conservative expansion estimate is imposed here.
Stopped identities retain their original clock and need no active-event phase.

The enforcement obligations remain explicit:

| Remaining conclusion | Owner / required evidence |
|---|---|
| Supplied target occupancy equals actual outgoing occupancy | A4 complete target authentication; clock equality alone is insufficient |
| Every intermediate live queue/RAM/output/request peak fits | A4/A5 constrained resource accounting at actual prefixes |
| Arbitrary independent event/read/write/allocation ceilings | A4/A5 exact occurrence/cost accounting, including padded writes and WRITE observations |
| Fixed pointer/length widths and cumulative persistent allocation | A5 queue/request installation; individual field-count ceilings are insufficient |
| Preserve `ExecutionPath.Encoded` when adding WRITE | The installed seven-handler proof derives the full predicate from each active CPU row and its actual replayed source. The full assembly must retain this grounding. |
| Physical height and every channel's occurrence ceiling | Exact inventory accounting below; final A4/A5/A6 construction must prove its full expansion fits, and silent tables need explicit height bounds |

These are unproved implementation obligations, not additional capstone premises. The endpoint
checker regression deliberately accepts a boundary whose tape exceeds the padded-write budget:
it prevents an endpoint-only check from being mistaken for complete resource enforcement.

## Exact physical accounting

`ToClean/Air/Footprint.lean` measures the public verifier's operations and every physical table.
For each raw channel, `channelOccurrences` adds the verifier's occurrence count to each table's
height times its circuit's syntactic interaction width. `channelOccurrences_eq_length` proves
this is exactly the evaluated ledger length. Repeated keys, zero multiplicities, refreshes and
inactive padding all spend capacity. No deduplication or multiplicity filter is involved.
`PhysicalFits` checks every table height and every registered channel against numeric ceilings;
`ChannelCapacity` is precisely Clean's existing strict field-characteristic bound.

The retained ordinary compiler consumes `ChannelCapacity` in `NativeTraceAdmissible` and its
functional completeness proof. `Proofs/Completeness/PhysicalFootprint.lean` proves its exact
height and demand formulas from the existing event buckets and provider occurrence lists:
one row per instruction event or provider occurrence, one mandatory Halt padding row, an empty
ordinary SyscallInstrs table, and the separate public verifier ledger. Provider closure and refresh occurrences are
already in those lists. The resulting `physicalFits_iff` and `channelCapacity_iff` are exact
arithmetic equivalences; they do not replace the accepted language with an upper estimate.

`Soundness/ResourceFootprint.lean` applies the same accounting to the installed host assembly.
Raw balance gives the native `p-1` occurrence ceiling on **every registered channel**, including
host/boundary channels. Any table with a positive syntactic interaction width on a registered
channel inherits its native height bound. A silent table needs separate evidence. Installing
the endpoint checker preserves every physical row and existing channel ledger. Its three
assertions add exactly six occurrences on a fresh channel. Thus the installed witness fits
exactly when the base witness fits and the channel ceiling is at least six. The lifting theorem
keeps this equivalence explicit for arbitrary budgets; the native field bound covers this cost.

In a nonempty address window the fixed RAM inventory has one row plus the number of changes
between neighboring byte values. The empty window has no logical rows. Every row covers
a nonempty run, and every byte has exactly one covering row. Any sound interval table
with complete coverage must contain at least as many rows. Clean pads the inventory to a
power of two and charges one occurrence per physical row. On KoalaBear the provider itself
fits exactly when there are fewer than $2^{30}$ interior changes.
[Maximal runs and minimality](../SP1Clean/Semantics/Memory/MemoryIntervals.lean) ·
[Installed RAM bound](../SP1Clean/Export/FixedRamCapacity.lean)

A region of $2^{29}$ identical nonzero bytes, surrounded by zeros, needs three runs and four
padded rows. An alternating-byte region can exceed $2^{30}$ changes while leaving both endpoints
within the native byte ceiling. In the checked alternating example the installed raw statement
fails for every public header and height vector, even though the empty release trace is valid.
[Capacity examples](../SP1CleanTest/Alignment/Core/FixedRamCapacity.lean)

For a public boundary payload ceiling of at most 536,871,036 bytes, the 125-byte minimum
boundary overhead and the bound of two changes per live byte give at most $2^{30}$ rows per
endpoint RAM provider. Each then leaves at least 1,056,964,608 occurrences on its own KoalaBear
channel. Every checked instruction also pays for a distinct live source byte. Every writable
gap ends at an instruction start or the address limit. Those facts bound each fixed Program and
permission provider by $2^{29}$ rows at the same ceiling. The whole-assembly preset must include
the remaining physical providers, consumers, public operations and padding on each channel.
[Fixed image capacity](../SP1Clean/Export/FixedImageCapacity.lean)

The source boundary pays an eight-byte length prefix and the actual payload of every initial
hint. That covers a node and every mandatory padded word in its fixed inventory, including the
extra word for aligned buffers. For any boundary ceiling at most $p-1$, each source provider has
at most $2^{28}$ physical rows. Its channel retains exactly one occurrence per row. Fresh nodes
allocated during the shard have a separate inventory and cost.
[Fixed hint providers](../SP1Clean/Export/FixedHintCapacity.lean)

## Representation and retirement

The only complete execution model is `ExecutionPath` over Sail/host/clock, with paired replay and
`ExecutionSnapshot` boundaries. New resource records measure it; they do not carry a second path.
`ExecutionResources` observes the existing replay, summing events/ticks/read/write/allocation work
and taking maxima for live resources. It includes both sides of each real step; empty identities
check their incoming occupancy separately. `resources_append` and `resources_split` prove the
arithmetic at complete semantic cuts. `ExecutionSnapshot.resources_realize` computes occupancy
without materializing dense Sail memory; `ByteMemory.supportBelow` removes zeros and shadowed
writes. Both state and tape usage are invariant under equivalent complete snapshots.

The release statement retains the existing `nativeProfile` and adds its separate per-jump
link encoding condition. [Release statement](../SP1Clean/FormalModel/ShardRelease.lean)

At the native preset, raw acceptance of the seven-handler assembly recovers a single tape whose
every prefix meets nine semantic ceilings. Events are bounded by elapsed ticks. HINT_READ pays
for the padded writes of the consumed hint prefix. Reads and fresh allocations are zero. The
four host occupancies are bounded by the incoming host inventory. For arbitrary limits, event
count and padded writes must each fit their own ceiling. Both endpoint payloads are checked.
Peak intermediate `boundaryBytes` remains a separate obligation because ordinary stores can
change the number of nonzero RAM bytes. [Installed seven-handler bounds](../SP1Clean/Export/InstalledExecutionResources.lean)

The same tape satisfies `ReleaseStatementExecution` if and only if this peak fits the native
ceiling. At arbitrary limits the exact criterion also compares event count and padded write bytes
with their respective ceilings. The row proofs establish the clock phase, the full ordinary
instruction encoding and the SP1 link-write condition. The raw statement supplies the complete
endpoints and the commitment declarations. [Release criterion](../SP1Clean/Export/InstalledExecutionResources.lean)

At every cut, the recovered tape's peak payload and the reached state's payload are at most
the incoming payload plus eight bytes per ordinary retirement in the prefix. A decoded store
can change at most eight byte addresses. HINT_READ consumes enough host payload to pay for the
entire padded write, and the Sail output is preserved. Hence a raw native shard of any duration
satisfies the complete native release statement whenever incoming payload plus elapsed ticks is at
most `SP1Prime - 1`. For raw acceptance at `fixedProviderPreset`, the verified incoming payload
is at most $2^{29}+124$ and the elapsed time is at most $2^{24}$ ticks. Their sum is below the
native ceiling. Thus every accepted shard at that preset has a complete release execution at the
broader native limits. The tighter preset's own peak and padded-write ceilings still require
separate checks. [Payload bound and capstone theorems](../SP1Clean/Export/InstalledBoundaryGrowth.lean)

Two normally retired RV64 byte stores witness the difference between endpoints and the peak.
The first writes one to a zero byte, and the second clears it. A carried stdout stream puts
both endpoints exactly at the native payload ceiling, `SP1Prime - 1`. The intermediate state
uses `SP1Prime` bytes. Both endpoint checks pass, both instructions are encoded, and all nine
other resource measurements fit. This example establishes the gap for a semantic execution.
Whether the installed AIR accepts a witness for this execution remains open.
[Two-store theorem](../SP1CleanTest/Alignment/Core/BoundaryPayload.lean)

For an accepted native shard with fewer than 16 elapsed public ticks, the tape is empty or
contains one ordinary instruction. Its complete release statement follows from the checked
endpoints. A running-to-stopped shard with fewer than 272 elapsed ticks contains exactly one
HALT, whose argument yields the public exit code. A chain of the shorter ordinary shards
retains each local release statement and concatenates their tapes across the complete
boundaries. These two endpoint clock conditions give instances of the public capstone
`SoundnessTarget` at any accepted header and table heights. Each shard keeps its own resource limits.
[Short-shard and HALT theorems](../SP1Clean/Export/ShortShard.lean) ·
[Chain theorem](../SP1Clean/Export/ShortShardChain.lean)

`nativeProfile` bounds the broader Sail execution. It requires width-aligned
ordinary LOAD/STORE spans and phase one modulo eight at each active CPU source. The installed seven-handler assembly proves both conditions at every replay cut.
Its load and store rows identify the actual RV64 base and signed offset, including loads to x0.
Their complete spans lie between the guest-memory endpoints. The clock phase implies
the low-clock window (`clock % 2^24 + 4 < 2^24`). Normal Sail retirement alone does not imply width alignment. Final PC/clock
fit their native encodings but need no subsequent fetch. [Accepted encoding](../SP1Clean/Soundness/HostFinalMemoryEncoding.lean)

Every HINT_READ with payload length `n` pays for exactly `n / 8` continuing words and one
final word, including empty and word-aligned payloads. In each physical word row the installed
circuit emits eight write-permission requests, two Memory occurrences, two host RAM occurrences
and twelve Byte occurrences. The call handler emits another twelve Byte occurrences. These
counts include padding and retain the cancelling RAM pair. At the separate demand heights of
these three tables, permission occurrences cost at most twice the charged write bytes, each RAM
ledger at most half, and Byte at most six times. Other producers and the providers also use
these shared channels. Whole-assembly capacity still requires their combined physical counts.
[Semantic charge](../SP1Clean/Semantics/Resources/HintReadDemand.lean) · [Physical bounds](../SP1Clean/Proofs/Completeness/HintReadCapacity.lean)

`fixedProviderPreset` retains the native event and tick ceilings and sets the boundary payload
ceiling to `2^29 + 124` bytes and cumulative write ceiling to `2^24` bytes. On any admissible
mixed path within that preset, the full verifier, all ten fixed providers and all three
demand-padded HINT_READ tables fit together. The verifier emits one pull per changed native
location, whose count is bounded by 32 register locations plus the two actual RAM supports.
Each ordinary event enters one of 25 chronological instruction buckets. Their independently
padded heights sum to at most twice the ordinary count. The observation consumer has one
active row per ordinary event, and the authenticated endpoints select one row across its three
terminal tables. [Constructed ordinary heights](../SP1Clean/Export/CompiledOrdinaryPreset.lean) · [Observation tables](../SP1Clean/Export/InstalledObservationPreset.lean)

| Installed tables covered alongside the verifier | Total tables covered | Minimum remaining occurrences per channel |
|---|---:|---:|
| Ten fixed providers and three HINT_READ tables | 13 | 822,082,528 |
| Also the protected ordinary instruction tables | 38 | 293,600,224 |
| Also the observation consumer and three terminal modes | 42 | 285,211,616 |
| Also MemoryBump and StateBump | 44 | 222,297,056 |

The mixed compiler records the raw CPU-state push and ordered register refreshes at each tape
position. A register access can refresh its preceding timestamp once, with at most three
refreshes per instruction or ECALL. A StateBump is selected exactly when the clock low limb
reaches `2^24` or either of the two lower PC limbs reaches `2^16`. A maximal upper clock or PC limb admits a lower-limb carry that
stops before reaching it. A carry into an already maximal upper limb exceeds 48 bits. At the preset the two
physical table heights are at most `2^23` for MemoryBump and `2^21` for StateBump. Both emit
six Byte occurrences per physical row, including padding. Each emits two occurrences on its
own Memory or State channel. Their constructed rows satisfy both circuits on shared prover data.
Capacity for the other 56 tables depends on their combined channel use. [Carry boundary examples](../SP1CleanTest/Alignment/Core/MixedStateBumpEdges.lean) · [Mixed bump inventory](../SP1Clean/Proofs/Completeness/MixedBumpInventory.lean) · [Physical tables](../SP1Clean/Export/InstalledBumpTables.lean) · [44-table bound](../SP1Clean/Export/InstalledBumpPreset.lean)

The compiler also projects active ECALL instruction inputs in chronological order. Lean proves
that the full-word code guard and all 65 instruction columns satisfy the bundled circuit's
prover assumptions, and that decoding each row recovers its complete syscall event. This
covers all eight host calls, including WRITE. Host-effect receipts and their physical tables
have separate construction and balance obligations. [ECALL trace theorem](../SP1Clean/Proofs/Completeness/MixedSyscallRows.lean)

At the native field, each released mixed execution supplies the 25 physical ordinary tables.
Their active rows carry the displaced values and timestamps from the mixed execution prefix.
Empty buckets have height zero. Each nonempty bucket receives its registered padding to the
next power of two. DivRem uses the released inactive divisor one. Every physical row issues a
successor receipt with unit weight on the event prefix and zero weight throughout the suffix.
Clean's canonicalization of the full inventory preserves their cells, local checks, guarantees
and all literal channel occurrences. Global balance still requires the matching providers and
consumers. [Mixed execution and installed tables](../SP1Clean/Proofs/Completeness/MixedInstructionTables.lean)

The physical `tableRows` and
`channelOccurrences` ceilings have actual witness consumers through `PhysicalFits`; they are
not yet derived from `nativeProfile` for the full mixed constructor. Semantic measurements do
not stand in for that proof. `boundaryBytes` is a variable-payload measure, not a full Sail
serialization-size theorem: fixed public register/platform data and the final boundary circuit's
actual row cost remain part of A4/R5. No bounded-ensemble instance is claimed by these definitions. `MemorySnapshot` remains the provider view.
`HintQueue.storeAfter?` constructs the persistent node store along the same complete replay,
including interleaved WRITE allocations, hook replies and HINT_READ pops. At every cut its size
equals the initial hint count plus cumulative allocations. The suffix reuses that store and
preserves every historical pointer. The native KoalaBear ceilings on those two terms imply that
the head and allocation frontier both fit 48 bits. Every historical hint was live when added.
The live-byte ceiling therefore bounds its length even after a pop. The canonical node record
and every padded word row fit their encodings and bind that hint in the final store.
Authentication of the new node and word rows
belongs to the mixed host assembly. [Persistent hint inventory](../SP1Clean/Proofs/Completeness/HintInventory.lean)

| Compatibility surface | Replacement / removal condition |
|---|---|
| `InstructionPlanReady`, `NativeCompilerReady` | Local success predicates of the retained builders; no occurrence in the new domain. Derive them from admissibility in the mixed compiler (C9) and remove them. |
| Explicit numeric range checks in older chip/Sail lemmas | Retain encoding-specific statements, derive their range facts from `NativeLayout`; factor more generally only with a migrated consumer. |

`ExecutionMemory` proves presence and outside-domain framing along the existing Sail/host path,
including padded host writes, independently of AIR grounding. `ShardAccess` derives canonical
access projection at every ordinary position. `Proofs/Completeness/SemanticAccess.admissibleExecution_compile_at`
then derives event extraction, role ordering, valid refreshes and the outgoing frontier invariant
for all 25 routed families. The family lemmas inspect the existing router and constructors;
`instructionAccessSlots` only erases values from the canonical plan. No second instruction model
or path is introduced. The release execution supplies the registered event validity for all
25 ordinary families at every cut, using the preceding mixed access frontier. Each active
link takes its bound from the release statement and each memory instruction obtains span and
alignment from the decoded access. The complete mixed table construction and its joint ledgers
remain A6. [Mixed instruction rows](../SP1Clean/Proofs/Completeness/ReleaseInstructionRows.lean)

Native range/resource strengthening does not by itself establish agreement with released SP1.
The native proofs and Rust comparison tests have separate scopes.
