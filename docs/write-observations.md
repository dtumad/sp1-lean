# Released WRITE observations

SP1 v6.10.0 reads the byte count from x12. It rounds the buffer address down to an eight-byte boundary and reads `ceil(((address % 8) + length) / 8)` words with `mr_slice_no_trace`. It converts each word to little-endian bytes, drops the head offset, and takes exactly the requested length. An unaligned, empty buffer consequently observes one word and emits zero bytes. Both JIT and portable implementations leave the cells' timestamps unchanged. The JIT register accessor reads x12 directly. [Released WRITE](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/write.rs#L186-L206) · [JIT accessors](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/jit/src/context.rs#L150-L212) · [Portable word observation](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/arch/portable/mod.rs#L176-L180)

The execution tracer records the ECALL's x11, x10 and x5 accesses. Its syscall dispatcher returns `Ok(None)` for WRITE. The released SyscallInstrs row has no x12 or buffer-word transition for WRITE. A compiler can recover the values of x12 and the covered RAM cells from the complete incoming Sail state and the genuine execution prefix. The native read-only observer recovers those same values from the authenticated incoming snapshot and preceding rows of the physical Memory history. [Released ECALL records](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/tracing.rs#L905-L931) · [Released syscall dispatch](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/vm/syscall.rs#L403-L413)

The native `HostCallChip` currently posts an additional x12 timestamp for WRITE. `HostRamReadChip` advances the predecessor timestamp of every traced RAM read. The installed six- and seven-call profiles exclude WRITE. Installing released WRITE requires connecting these read-only operands to an active WRITE handler while retaining the released Memory history.

The local host boundary stores raw stdout/stderr bytes before the released formatter's UTF-8 conversion and line-oriented output. Public-value bytes append to the public output, and descriptor 14 prepends the buffer to the hint queue. Seven builtin hook descriptors consume the next declared reply only when its low-u32 descriptor and input bytes match. The returned hints precede the existing queue in the declared order. Matching a transcript authenticates that request and response association. Proving that the released builtin computes those response bytes requires formalizing each hook or explicitly binding an external result. The semantic construction uses this existing transcript boundary. [Released descriptor dispatch](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/core/executor/src/minimal/write.rs#L209-L242) · [Descriptor values](https://github.com/succinctlabs/sp1/blob/d83ed91f96701209613720708f36ffce0e98ed33/crates/primitives/src/consts.rs#L95-L144)

The `WriteObservations.of_admissibleExecution` theorem constructs the released read packet at every actual WRITE cut, decodes the exact little-endian slice, and proves the descriptor effect. The executable observer’s `read?_eq_some_iff` theorem characterizes its accepted packets by the actual x12 value and every ordered word in that same Sail state. The `traced_x12_incompatible` and `traced_ram_incompatible` theorems identify the timestamp changes a released WRITE adapter must avoid. [Kernel-checked construction](../SP1Clean/Proofs/Completeness/WriteObservations.lean)

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

## Read-only probe demand

Along a successful execution, let `C` count WRITE packets, `W` count the aligned words
in those packets and `B` count the bytes requested through x12. The packet lengths sum
to the existing `readBytes` charge. Each ECALL consumes 264 ticks and rounding the two
buffer endpoints gives `8W ≤ B + 14C`. These bounds cover ignored descriptors as well as
callbacks and ordinary outputs.

At `fixedProviderPreset`, `C ≤ 63,550` and `W ≤ 266,449,516`. Together at most
266,513,066 x12 and RAM probes fit a power-of-two height of `2^28` if a table uses one
row per probe. Shared-channel capacity for a physical observer depends on the interactions
emitted by its actual rows. [Semantic packet accounting](../SP1Clean/Proofs/Completeness/WriteProbeDemand.lean) · [Preset bound](../SP1Clean/Export/WriteProbeCapacity.lean)
