# Released WRITE observations

SP1 v6.10.0 reads the byte count from x12. It rounds the buffer address down to an eight-byte boundary and reads `ceil(((address % 8) + length) / 8)` words with `mr_slice_no_trace`. It converts each word to little-endian bytes, drops the head offset, and takes exactly the requested length. An unaligned, empty buffer consequently observes one word and emits zero bytes. Both JIT and portable implementations leave the cells' timestamps unchanged. The JIT register accessor reads x12 directly. [Released WRITE](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/write.rs#L186-L206) · [JIT accessors](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/jit/src/context.rs#L150-L212) · [Portable word observation](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/arch/portable/mod.rs#L176-L180)

The execution tracer records the ECALL's x11, x10 and x5 accesses. Its syscall dispatcher returns `Ok(None)` for WRITE. The released SyscallInstrs row has no x12 or buffer-word transition for WRITE. A compiler can recover the values of x12 and the covered RAM cells from the complete incoming Sail state and the genuine execution prefix. The native read-only observer recovers those same values from the authenticated incoming snapshot and preceding rows of the physical Memory history. [Released ECALL records](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/tracing.rs#L905-L931) · [Released syscall dispatch](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/vm/syscall.rs#L403-L413)

The native `HostCallChip` publishes the incoming clock, raw syscall code, x10, x11 and returned x5. Its complete Memory ledger equals that of the released instruction for every physical row, including padding. `HostRamReadChip` advances the predecessor timestamp of every traced RAM read. The installed six- and seven-call profiles exclude WRITE. Installing released WRITE requires connecting these read-only operands to an active WRITE handler while retaining the released Memory history.

The local host boundary stores raw stdout/stderr bytes before the released formatter's UTF-8 conversion and line-oriented output. Public-value bytes append to the public output, and descriptor 14 prepends the buffer to the hint queue. Seven builtin hook descriptors consume the next declared reply only when its low-u32 descriptor and input bytes match. The returned hints precede the existing queue in the declared order. Matching a transcript authenticates that request and response association. Proving that the released builtin computes those response bytes requires formalizing each hook or explicitly binding an external result. The semantic construction uses this existing transcript boundary. [Released descriptor dispatch](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/write.rs#L209-L242) · [Descriptor values](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/primitives/src/consts.rs#L95-L144)

The `WriteObservations.of_admissibleExecution` theorem constructs the released read packet at every actual WRITE cut, decodes the exact little-endian slice, and proves the descriptor effect. The executable observer’s `read?_eq_some_iff` theorem characterizes its accepted packets by the actual x12 value and every ordered word in that same Sail state. The `HostCallProjection.memory_values` theorem preserves every ECALL Memory interaction. The `traced_ram_incompatible` theorem identifies the timestamp change produced by a traced RAM read. [Kernel-checked construction](../SP1Clean/Proofs/Completeness/WriteObservations.lean)

At a physical cut, `wordAt` starts with the supplied snapshot and scans only preceding active rows in State-channel order. It takes the value of a push at the architectural effect slot for the queried key. When no such push exists, the row’s grounded read-backs and frame proof preserve the held value. The proof uses the original messages of active guest events, including HINT_READ RAM effects. All padding occurrences and weights stay in the canonical ledger. Multiple probes can use the same preceding write, including at the same cut. [Physical prefix proof](../SP1Clean/Soundness/WriteObservationHistory.lean)

The native `checkWriteInputs` procedure compares the proposed code, descriptor, and address with x5, x10, and x11. It compares the four proposed x12 limbs and every aligned word with the same prefix. `makePacket?` computes the length and word limbs from that history. `installed_cuts` derives the predecessor state for each cut of the currently supported host assembly from its constraints and balanced channels. State-channel ordering is proof-derived. The packet procedure runs on supplied ordered rows. Installing WRITE in the eight-call AIR still requires wiring the read-only observations to an active ECALL, constraining the descriptor effects and hook boundary, and discharging the extended row and ledger proofs. [Packet checker and constructor](../SP1Clean/Proofs/Completeness/WriteObservationPacket.lean) · [Installed-prefix theorem](../SP1Clean/Proofs/Completeness/WriteObservationCuts.lean)

## Committed public values and complete host effects

The guest library hashes the bytes passed to the public-values descriptor after issuing WRITE.
At HALT it emits eight COMMIT words. The released instruction AIR binds each selected digest
word to x11, and the SDK checks the hash of the supplied public-value bytes against that digest.
This is the release-facing public output contract. A guest can also issue ECALL directly.
The stronger native host contract tracks the actual buffer at each WRITE, raw stdout/stderr
bytes, queued hints and matched requests and replies. Values enqueued by WRITE can affect a
later HINT_READ even when the caller only inspects the final guest state.
[Guest WRITE wrapper](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/zkvm/entrypoint/src/syscalls/io.rs#L13-L31) · [Guest HALT](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/zkvm/entrypoint/src/syscalls/halt.rs#L24-L42) · [COMMIT AIR](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/machine/src/syscall/instructions/air.rs#L350-L367) · [SDK verification](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/sdk/src/prover.rs#L172-L220)

Lean exposes the SDK check as `StockPublicOutput.acceptsCore` for a list of typed Core shard
records and `Claim.accepts` for the exit code and digest shared by Core and Compressed. The last
Core record supplies the claim. Its 32 bytes match either SHA-256 or BLAKE3 of the supplied
public bytes. The default status requires success. The native header and the release commitment
adapter project to the same claim when their exit codes agree. Version, layout and cryptographic
proof checks surround this public-output check in the SDK.
[Formal statement](../SP1Clean/FormalModel/Contracts/StockPublicOutput.lean) · [Release-vector tests](../SP1CleanTest/Core/StockPublicOutput.lean)

## Physical memory versions

Each incoming CPU clock falls between two successive effect-slot pushes at a given register
or RAM location. The original typed Memory messages supply both clocks and the held four-limb
word. The incoming snapshot supplies the first value. The final version extends through the
outgoing cut. If a location has no effect-slot push, its snapshot value covers every cut.
The interval inventory preserves repeated pushes in physical order. From the installed
constraints and ledger balance, Lean identifies the unique clock-selected version with the
paired Sail state. The packet theorem applies that join to x12 and to every aligned buffer
word, including when several calls observe the same cell.
[Physical intervals](../SP1Clean/Soundness/WriteVersionIntervals.lean) · [Installed cut theorem](../SP1Clean/Proofs/Completeness/WriteObservationCuts.lean) · [Packet characterization](../SP1Clean/Proofs/Completeness/WriteObservationPacket.lean)

At SP1's finer Memory-record times an access supplies its pulled word from the previous clock
up to its own push. The last pushed word survives after that time. The existing per-location
balance proof supplies these record handoffs even for aliased touch slots. A native AIR provider
can use the consecutive version boundaries for a private lookup keyed by location and time.
It still has to authenticate complete boundary coverage, including the absence of prior effects
for a source-only location, register the observer alongside the physical producers, and
constrain the host effects of the selected packet.
[Typed Memory record intervals](../SP1Clean/Proofs/Completeness/MemoryVersionHistory.lean)

## Native probe table

An active `WriteProbe.component` row pulls one private version containing the location, a
closed clock interval, and a four-limb word. The circuit enforces a canonical x12 or aligned
RAM key, 16-bit limbs, and inclusive integer clock comparisons. It pushes the same key and
word together with the absolute incoming clock. The demand guard compares that full receipt
with the requested read. Padding gives both messages zero multiplicity. Probes use neither
a guest event nor a new guest Memory timestamp.
[Observer circuit](../SP1Clean/Proofs/Operations/WriteProbe.lean) · [Physical signed messages](../SP1Clean/Proofs/Operations/WriteProbeLedger.lean)

`installed_table` builds an ordinary Clean table from a finite list of requests at checked
physical execution cuts. Repeated requests retain their positions and values. Genesis admits
clock zero and a final version admits the largest 48-bit clock. When a physical provider
offers a smaller range inside an authentic version, `installed_read_of_restriction` identifies
the checked result with the held Sail word at the same cut. The enclosing host assembly must
authenticate every version supply and balance both private channels.
[Interval encoding and replay](../SP1Clean/Proofs/Completeness/WriteProbeInputs.lean) · [Table generation](../SP1Clean/Proofs/Completeness/WriteProbeTables.lean)

## Physical sources

The two verifier-fixed x12 rows bind the first and last CPU cuts to the actual snapshot
register. Register refreshes retain both original bus timestamps and the unchanged word.
The ordinary, ECALL and HINT_READ components publish each original Memory predecessor from
its previous timestamp through the incoming CPU clock. A genuine push at the incoming
clock is value-preserving. The eight-tick gap between CPU cuts ensures that truncating a
mutating access's predecessor interval at its incoming clock retains every eligible probe.
The chronological selector picks the first later push, or the final suffix when none exists.
[Incoming-cut proof and selector](../SP1Clean/Proofs/Completeness/WriteAccessIntervals.lean)

Both ordered finalizers publish the actual last Memory record through the largest 48-bit
clock. Valid queries outside the touched inventory enter both sorted boundaries. The batch
builder runs the source and final circuits at every new key and returns their physical row
arrays. The snapshot circuit supplies the authentic zero-timestamp word. Its unit Memory push
cancels the finalizer's unit pull, and the suffix covers every representable clock.
[Sparse boundary construction](../SP1Clean/Proofs/Completeness/WriteSparseBoundaries.lean) · [Fixed x12 rows](../SP1Clean/Native/Operations/WriteProbeRegisterBoundary.lean)

The 25 protected ordinary families, ECALL, both HINT_READ word variants, the register refresh
and both ordered finalizers form a 31-component source group. The raw LogUp bound counts
the supplier height plus each source height times its number of pull sites, including padding.
When this total fits the prime field, raw receipt balance and the supplier’s physical constraints
trace each positive version to a specific original source. All original guest Memory multiplicities and padding are preserved. At canonical
ordinary-block data, mixed execution constructs each protected ordinary table with one to
three predecessor occurrences on every physical row. ECALL contributes three and each
HINT_READ word contributes one. The observer installs each publisher at its original physical position. Projecting an accepted native
witness back to the supervisor still requires recovering its State and Memory histories alongside the eighth host receiver.
[Source inventory](../SP1Clean/Soundness/WriteAccessInventory.lean) · [Mixed ordinary construction](../SP1Clean/Proofs/Completeness/WriteOrdinaryTables.lean) · [Mixed refresh construction](../SP1Clean/Export/WriteRefreshTables.lean)

## Read-only probe demand

Along a successful execution, let `C` count WRITE packets, `W` count the aligned words
in those packets and `B` count the bytes requested through x12. The packet lengths sum
to the existing `readBytes` charge. Each ECALL consumes 264 ticks and rounding the two
buffer endpoints gives `8W ≤ B + 14C`. These bounds cover ignored descriptors as well as
callbacks and ordinary outputs.

At `fixedProviderPreset`, `C ≤ 63,550` and `W ≤ 266,449,516`. Together at most
266,513,066 x12 and RAM probes fit a power-of-two height of `2^28` for the native table's
one row per probe. Each physical row contributes one occurrence to each of its two private
channels, including zero-weight padding. [Semantic packet accounting](../SP1Clean/Proofs/Completeness/WriteProbeDemand.lean) · [Preset bound](../SP1Clean/Export/WriteProbeCapacity.lean)

## Physical buffer coverage

Each native buffer span consumes the authenticated WRITE header. It seeds a cursor at
`address / 8` and closes it at `(address + length + 7) / 8`, using the full byte sum.
Each buffer word consumes one read-only receipt for the aligned RAM address at the
incoming ECALL clock and advances that cursor by one. Balance forces every index in
the interval to occur exactly once. An empty unaligned buffer observes its containing
word. An empty aligned buffer at `2^48` has no word rows and preserves the one-past
endpoint. The span and word rows forward the complete checked header and raw word to
the host-effect receivers. [Physical components](../SP1Clean/Proofs/Operations/WriteBufferPhysical.lean) · [Exact coverage](../SP1Clean/Soundness/WriteBufferCoverage.lean) · [Table construction](../SP1Clean/Proofs/Completeness/WriteBufferTables.lean)

## Native stream and queue endpoints

The native observer decorates 31 of the supervisor’s 98 tables and registers 15 additional
tables. Its classified WRITE header opens a guest interval at the incoming ECALL clock.
Each grouped word consumes its original eight observed lanes. The receipt checks the selected
lanes against one or two aligned destination blocks and checks the last block's actual extent.
This preserves empty and ignored writes, repeated positions, and writes crossing a block
boundary. The public verifier seeds all four chronological counters and requires the final
stdout, stderr, public-output and hook positions from the two snapshots. Hook metadata includes
the supplied reply's descriptor, request length and number of returned hints. A direct hint or a
hook emits a queue-allocation ticket. The current registry has no receiver for that ticket.
A nonempty direct hint also needs a block producer for its fresh pointer. These two obligations
remain before the assembled eight-call statement can cover queue-changing writes.
[Observer assembly](../SP1Clean/Export/WriteObservationAssembly.lean) · [Grouped row construction](../SP1Clean/Proofs/Completeness/WriteGroupRows.lean) · [Rows from an admitted WRITE](../SP1Clean/Proofs/Completeness/WriteWindowTape.lean)

At the native read and tick limits the call demand pads to at most `2^16` rows and grouped
word demand to at most `2^28`. Each word emits two physical block occurrences. Decoding
and dispatch spend four shared SP1 Byte occurrences per padded word and per padded call,
respectively. Fixed payload blocks and metadata rows fit heights `2^29` and `2^30` under the
existing endpoint budgets. These bounds measure this fragment. Other components on the same
channel also contribute to the complete assembly total.
[Joint occurrence formula](../SP1Clean/Proofs/Completeness/WritePlacementCapacity.lean) · [Paid fixed heights](../SP1Clean/Proofs/Completeness/WriteFixedDataCapacity.lean)

To recover the outgoing hints, follow the final private head through the persistent store.
Each node lookup fixes its tail and length. Each word lookup fixes eight bytes and the
last-word flag, including the padding word of an empty hint. Reaching pointer zero after
the last target buffer establishes equality of the complete queue. This permits a final
head or allocation frontier larger than the queue length after a pop.
[Snapshot lookup characterization](../SP1Clean/Semantics/Host/HintQueueSnapshot.lean)

The native assembly installs one fixed row per outgoing padded word and a single terminal
row. The terminal consumes the complete private queue state, starts the word walk at its
actual head, and requires the last cursor to reach zero. Every word takes its ordinal,
flags, byte length and contents from the public target. The constructor follows the actual store after replay, including surviving allocations.
The generated word and seal tables satisfy the local constraints and close the complete
signed walk ledger, including padded zero multiplicities. The seal consumes the private
head, allocation frontier and clock exactly once. The next shard starts from its own
canonical numbering of that target. The boundary payload covers all padded words,
giving a physical reader height of at most `2^26` under the fixed-provider preset.
[Physical reader](../SP1Clean/Native/Operations/HintQueueSnapshot.lean) · [Constructive ledger](../SP1Clean/Proofs/Completeness/HintSnapshotLedger.lean) · [Capacity](../SP1Clean/Export/HintSnapshotCapacity.lean)

The full native acceptance theorem still needs to connect consecutive WRITE clocks, close
all per-stream positions, and recover the persistent node and word sources for the
terminal walk from the balanced physical tables. The stock SDK digest statement above applies independently.
