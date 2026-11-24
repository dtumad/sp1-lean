import SP1Clean.FormalModel.Contracts.WriteStreamPositions
import SP1Clean.Proofs.Completeness.WriteWindowTape
import SP1Clean.Proofs.Completeness.WriteStreamExecution
import SP1Clean.Proofs.Completeness.HintInventory

/-! # Place guest words at their actual shard-wide stream positions

A second output call may begin in the last block of the preceding call. Each block must
therefore come from the complete public stream. Hook input uses the next consumed reply;
a direct hint instead names the next private allocation and starts its own byte string.
-/

namespace SP1Clean.WriteEffects

open Semantics Machine FormalModel.Shard TraceGen Soundness

/-- Output bytes already placed in this shard. Each request or private hint has its own origin. -/
def destinationOffset (route : WriteRoute) (earlier : WriteStreams) : Nat :=
  match route with
  | .stdout => earlier.stdout.length
  | .stderr => earlier.stderr.length
  | .publicValues => earlier.publicOutput.length
  | _ => 0

private theorem offset_of_no_key (route : WriteRoute) (earlier : WriteStreams)
    (none : destinationKey route earlier.hooks.length = .none) : destinationOffset route earlier = 0 := by
  cases route <;> simp_all [destinationKey, destinationOffset]

/-- A hook uses its ordinal in the supplied reply prefix. A direct hint uses the next
permanent node identity, even after a queue pop. -/
def destinationOwner (route : WriteRoute) (earlier : WriteStreams) (store : HintQueue.Store) : Nat :=
  match route with
  | .hook _ => earlier.hooks.length
  | .hint => store.size + 1
  | _ => 0

/-- Outputs and hook inputs take their bytes from the public endpoint stream.
The direct-hint and ignored routes use the observed guest payload. -/
def destinationBytes (route : WriteRoute) (earlier full : WriteStreams) (payload : Bytes) : Bytes :=
  ((destinationKey route earlier.hooks.length).bind (StreamKey.contents full)).getD payload

private theorem destination_split {route : WriteRoute} {host next : HostState} {payload : Bytes}
    (effect : route.Effect host payload next) (earlier later : WriteStreams) :
    let full := earlier.append ((WriteStreams.ofEvent route host payload).append later)
    ∃ before after : Bytes, destinationOffset route earlier = before.length ∧
      destinationBytes route earlier full payload = before ++ payload ++ after ∧
      ∀ k, destinationKey route earlier.hooks.length = some k → k.contents full = some (before ++ payload ++ after) := by
  cases route with
  | stdout => exact ⟨earlier.stdout, later.stdout, rfl, (List.append_assoc ..).symm, by intro k h; cases h; simp [WriteStreams.ofEvent, WriteStreams.append, StreamKey.contents, List.append_assoc]⟩
  | stderr => exact ⟨earlier.stderr, later.stderr, rfl, (List.append_assoc ..).symm, by intro k h; cases h; simp [WriteStreams.ofEvent, WriteStreams.append, StreamKey.contents, List.append_assoc]⟩
  | publicValues => exact ⟨earlier.publicOutput, later.publicOutput, rfl, (List.append_assoc ..).symm, by intro k h; cases h; simp [WriteStreams.ofEvent, WriteStreams.append, StreamKey.contents, List.append_assoc]⟩
  | ignored | hint => exact ⟨[], [], rfl, by simp [destinationBytes, destinationKey], by intro k h; cases h⟩
  | hook fd =>
    obtain ⟨returned, remaining, replies, _⟩ := effect
    have request : (StreamKey.request earlier.hooks.length).contents
        (earlier.append ((WriteStreams.ofEvent (.hook fd) host payload).append later)) = some payload := by
      simp [StreamKey.contents, WriteStreams.ofEvent, WriteStreams.append, replies]
    exact ⟨[], [], rfl, by simp [destinationBytes, destinationKey, request], by
      intro k h; cases h; simpa using request⟩

private theorem block_of_window {p : ℕ} [Fact p.Prime] (octets : Octets (ZMod p))
    (sink owner first size base : Nat) (dest : Bytes) {key : StreamKey} {full : WriteStreams}
    (coords : key.coordinates = (sink, owner, 0)) (found : key.contents full = some dest)
    (within : base + size ≤ dest.length) (right : Bool) :
    let row := Group.populate octets (sink : ZMod p) (Address.ofNat owner) first size base dest
    (if right then row.rightGate else row.leftGate) = 1 → row.block right ∈ dataBlocks full := by
  dsimp only
  intro enabled
  apply (dataBlocks_iff ..).mpr
  let index := if right then base / 8 + 1 else base / 8
  refine ⟨key, dest, index, found, ?_, ?_⟩
  · cases right with
    | false =>
      have nonempty : size ≠ 0 := by
        rintro rfl
        simp [Group.leftGate, Group.populate, SlicePlan.ofNat] at enabled
      dsimp [index]
      omega
    | true =>
      have cross : 8 < size + base % 8 := by
        by_contra no
        simp [Group.rightGate, Group.populate, SlicePlan.ofNat, no] at enabled
      dsimp [index]
      omega
  · cases right <;> simp only [Group.block, Group.populate, encodeBlock, coords, index, Bool.false_eq_true,
      ↓reduceIte, Address.ofNat_zero]
    all_goals rfl

private theorem packet_blocks {p : ℕ} [Fact p.Prime] (route : WriteRoute) (earlier full : WriteStreams)
    (store : HintQueue.Store) (clk address length : Nat) (buffer : List (BitVec 64)) (start : Nat) (dest : Bytes)
    (count : buffer.length = WriteObservations.wordCount address length) (paid : start + length ≤ dest.length)
    (key : StreamKey) (selected : destinationKey route earlier.hooks.length = some key) (found : key.contents full = some dest) :
    ∀ row ∈ packetGroups clk address length (effectSink route : ZMod p) (Address.ofNat (destinationOwner route earlier store)) buffer start dest,
      ∀ right : Bool, (if right then row.rightGate else row.leftGate) = 1 → row.block right ∈ dataBlocks full := by
  have coords : key.coordinates = (effectSink route, destinationOwner route earlier store, 0) := by
    cases route <;> cases selected <;> rfl
  intro row member right
  obtain ⟨⟨word, i⟩, m, rfl⟩ := List.mem_map.mp member
  have inside := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp m)).1
  have last : i < (address % 8 + length + 7) / 8 := by simpa only [count, WriteObservations.wordCount] using inside
  have within : start + (8 * (address / 8 + i) + (window address length (address / 8 + i)).1 - address) +
      (window address length (address / 8 + i)).2 ≤ dest.length := by
    dsimp only [window]
    omega
  exact block_of_window _ _ _ _ _ _ _ coords found within right

/-- At every actual WRITE, the word rows use the exact bytes and starting position in the
shard-wide output, hook request, or newly allocated hint. The route, pointer, offset and
unaligned block contents are determined by the run and both public host endpoints. -/
theorem native_destination_groups {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    ∃ current length buffer cursor,
      executionTrajectory (policy SP1Prime image) image.program source.realize events cut = some current ∧
      WriteObservations.read? current.sail call = some (length, buffer) ∧
      HintQueue.storeAfter? (policy SP1Prime image) image.program source.realize (events.take cut)
        (HintQueue.ofList source.host.io.hints) = some cursor ∧
      let route := WriteRoute.ofDescriptor call.arg1
      let earlier := WriteStreams.fromEndpoints source.host current.host
      let full := WriteStreams.fromEndpoints source.host target.host
      let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
      let dest := destinationBytes route earlier full bytes
      let groups := packetGroups current.clock call.arg2.toNat length.toNat (effectSink route : ZMod SP1Prime)
        (Address.ofNat (destinationOwner route earlier cursor.1)) buffer (destinationOffset route earlier) dest
      (∀ key, destinationKey route earlier.hooks.length = some key → key.contents full = some dest) ∧
      groups.length = buffer.length ∧ groups.map (·.octets) =
        (effectRows (p := SP1Prime) current.clock call.arg1 call.arg2 length buffer).2.map (WordRow.octets (256 : ZMod SP1Prime)⁻¹) ∧
      (∀ row ∈ groups, row.Valid ∧ row.HonestCoordinates) ∧
      ∀ key, destinationKey route earlier.hooks.length = some key → ∀ row ∈ groups, ∀ right : Bool,
        (if right then row.rightGate else row.leftGate) = 1 → (blockTable (p := SP1Prime) full).Contains (row.block right) := by
  obtain ⟨current, next, length, buffer, read, currentAt, nextAt, effect, _⟩ := groups_of_admissibleExecution run present write
  obtain ⟨_, cursor, _, _, beforeStore, _, _, _, _, _, _, _, _, _⟩ := admissibleExecution_hintInventory run cut
  let route := WriteRoute.ofDescriptor call.arg1
  let earlier := WriteStreams.fromEndpoints source.host current.host
  let later := WriteStreams.fromEndpoints next.host target.host
  let full := WriteStreams.fromEndpoints source.host target.host
  let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
  obtain ⟨a, left, _⟩ := run.1.2.split cut
  obtain ⟨b, toNext, right⟩ := run.1.2.split (cut+1)
  have sameBefore : a = current := Option.some.inj (left.replay.symm.trans currentAt)
  have sameAfter : b = next := Option.some.inj (toNext.replay.symm.trans nextAt)
  subst a b
  have joined : full = earlier.append ((WriteStreams.ofEvent route _ bytes).append later) :=
    ((execution_streams left).append ((WriteStreams.ofEvent_binds effect).append (execution_streams right))).unique
  obtain ⟨before, after, offset, placed, keys⟩ := destination_split effect earlier later
  rw [← joined] at placed keys
  change destinationOffset route earlier = before.length at offset
  change destinationBytes route earlier full bytes = before ++ bytes ++ after at placed
  change ∀ k, destinationKey route earlier.hooks.length = some k → k.contents full = some (before ++ bytes ++ after) at keys
  obtain ⟨_, _, lower, upper, bufferCount, _⟩ := WriteObservations.read?_eq_some_iff.mp read
  refine ⟨_, length, buffer, cursor, currentAt, read, beforeStore, ?_⟩
  dsimp only
  refine ⟨fun k h => (keys k h).trans (congrArg some placed.symm), packetGroups_length .., packetGroups_octets .., ?_⟩
  have width : before.length + length.toNat < 2^48 := by
    cases selected : destinationKey route earlier.hooks.length with
    | none =>
      have empty := offset_of_no_key route earlier selected
      omega
    | some key =>
      have content := keys key selected
      have found : (Query.length key).lookup full = some (before ++ bytes ++ after).length := by
        rw [Query.lookup, content]; rfl
      have size := Query.fits_of_inventory (admissible_inventoryOK run) found
      have lengthOf : bytes.length = length.toNat := WriteObservations.payload_length bufferCount
      have := size.2.2.2
      simp only [List.length_append, lengthOf] at this
      omega
  constructor
  · change ∀ r ∈ packetGroups _ _ _ _ _ _ (destinationOffset route earlier) (destinationBytes route earlier full bytes), _
    rw [offset, placed]
    exact packetGroups_honest _ _ _ _ _ _ before after width lower upper bufferCount
  · intro key selected row member right enabled
    apply ((blockTable (p := SP1Prime) full).contains_iff _).mpr
    change row.block right ∈ (if inventoryOK full then dataBlocks (p := SP1Prime) full else [])
    rw [ite_eq_left (admissible_inventoryOK run)]
    change row ∈ packetGroups _ _ _ _ _ _ (destinationOffset route earlier) (destinationBytes route earlier full bytes) at member
    rw [offset, placed] at member
    have size : bytes.length = length.toNat := WriteObservations.payload_length bufferCount
    exact packet_blocks route earlier full cursor.1 _ _ _ _ before.length (before ++ bytes ++ after) bufferCount
      (by simp [size]) key selected (keys key selected) row member right enabled

end SP1Clean.WriteEffects
