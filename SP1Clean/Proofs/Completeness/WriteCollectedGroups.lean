import SP1Clean.Proofs.Completeness.WriteBlockRequests

/-! # All grouped guest-word placements of a chronological WRITE collection

The collected dispatcher supplies the stream offset, hook ordinal and fresh private pointer.
The verifier's endpoint supplies public bytes. Every original guest read yields one complete
physical group, even when the descriptor is ignored or the occupied byte window is empty.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation Soundness.Target
private abbrev F := ZMod SP1Prime

private def readKey (route : WriteRoute) (reply : Nat) : Option StreamKey :=
  match route with
  | .stdout => some .stdout
  | .stderr => some .stderr
  | .publicValues => some .publicOutput
  | .hook _ => some (.request reply)
  | _ => none

private def selectedOwner (route : WriteRoute) (dispatch : Dispatch F) : fields 3 F :=
  match route with
  | .hint => dispatch.pointer
  | .hook _ => dispatch.baseCounter
  | _ => 0

private def fromPacket (full : WriteStreams) (d : Dispatch F) (packet : WriteObservations.Packet) : List (Group F) :=
  let h := d.request.header
  let route := WriteRoute.ofDescriptor h.descriptor.toBitVec64
  let address := h.address.toBitVec64.toNat
  let bytes := WriteObservations.payload packet.2 address packet.1.toNat
  let key := readKey route (Address.toNat d.baseCounter)
  packetGroups (Address.toNat h.clock) address packet.1.toNat (effectSink route : F) (selectedOwner route d)
    packet.2 (Address.toNat d.basePosition) ((key.bind (StreamKey.contents full)).getD bytes)

/-- All guest groups other than private direct hints. An ignored packet still retains the
positions of all its aligned reads. -/
def Entry.publicGroups (full : WriteStreams) (e : Entry) : List (Group F) :=
  if e.dispatch.flags.direct = 1 then [] else fromPacket full e.dispatch e.packet

/-- The single chronological table uses either the direct or public route for each entry.
Every guest group retains the original event/word order. -/
def Entry.placementGroups (full : WriteStreams) (e : Entry) : List (Group F) :=
  e.directGroups ++ e.publicGroups full

private theorem packet_owner (route : WriteRoute) (d : Dispatch F) (earlier : WriteStreams) (store : HintQueue.Store)
    (ptr : d.pointer = Address.ofNat (store.size+1)) (base : d.baseCounter = Address.ofNat (previousCount route earlier)) :
    selectedOwner route d = Address.ofNat (destinationOwner route earlier store) := by
  cases route <;> first | exact ptr | exact base | exact Address.ofNat_zero.symm

private theorem packet_eq {fd address len : BitVec 64} {clk prev : Nat} {earlier full : WriteStreams}
    {host : HostState} {store : HintQueue.Store} {buf : List (BitVec 64)}
    (time : clk < 2^48) (fits : streamCost earlier < 2^48) :
    let route := WriteRoute.ofDescriptor fd
    fromPacket full (dispatchRow fd address len clk prev earlier host store) (len,buf) =
      packetGroups clk address.toNat len.toNat (effectSink route : F) (Address.ofNat (destinationOwner route earlier store))
        buf (destinationOffset route earlier) (destinationBytes route earlier full (WriteObservations.payload buf address.toNat len.toNat)) := by
  let d := dispatchRow fd address len clk prev earlier host store
  let route := WriteRoute.ofDescriptor fd
  have addressDecoded : d.request.header.address.toBitVec64 = address := toBitVec64_bitVecToWord _
  have fdDecoded : d.request.header.descriptor.toBitVec64 = fd := toBitVec64_bitVecToWord _
  have clockDecoded : Address.toNat d.request.header.clock = clk := Address.toNat_ofNat _ time
  have hooks := count_hooks_le earlier.hooks
  unfold streamCost at fits
  have countFits : previousCount route earlier < 2^48 := by cases route <;> simp [previousCount,destinationOffset] <;> omega
  have offsetFits : destinationOffset route earlier < 2^48 := by cases route <;> simp [destinationOffset] <;> omega
  have count : Address.toNat d.baseCounter = previousCount route earlier := Address.toNat_ofNat _ countFits
  have offset : Address.toNat d.basePosition = destinationOffset route earlier := Address.toNat_ofNat _ offsetFits
  have ownerEq := packet_owner route d earlier store rfl rfl
  have keyEq : readKey route (previousCount route earlier) = destinationKey route earlier := by cases route <;> rfl
  change fromPacket full d (len,buf) = packetGroups clk address.toNat len.toNat (effectSink route : F)
    (Address.ofNat (destinationOwner route earlier store)) buf (destinationOffset route earlier)
    (destinationBytes route earlier full (WriteObservations.payload buf address.toNat len.toNat))
  simp only [fromPacket,addressDecoded,fdDecoded,clockDecoded,count,offset]
  change packetGroups _ _ _ _ (selectedOwner route d) _ _ ((readKey route (previousCount route earlier)).bind _ |>.getD _) = _
  rw [ownerEq,keyEq]
  rfl

private theorem paid_prefix {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {i : Nat} {current : ExecutionState} (reached : executionTrajectory (policy SP1Prime image) image.program source.realize events i = some current) :
    streamCost (.fromEndpoints source.host current.host) < 2^48 := by
  obtain ⟨same,left,right⟩ := run.1.2.split i
  cases Option.some.inj (reached.symm.trans left.replay)
  have bound := admissible_streamCost run
  have split := ((execution_streams left).append (execution_streams right)).unique
  change WriteStreams.fromEndpoints source.host target.host = (WriteStreams.fromEndpoints source.host current.host).append (WriteStreams.fromEndpoints current.host target.host) at split
  rw [split] at bound
  simp only [streamCost,WriteStreams.append,List.length_append,List.map_append,List.sum_append] at bound ⊢
  omega

private theorem ignored_silent {clk addr len : Nat} {owner : fields 3 F} {buf : List (BitVec 64)} {start : Nat} {dest : Bytes}
    {g : Group F} (member : g ∈ packetGroups clk addr len 0 owner buf start dest) : directRequests g = [] := by
  obtain ⟨⟨w,i⟩,_,rfl⟩ := List.mem_map.mp member
  simp [directRequests,Group.leftGate,Group.rightGate,Group.populate]

/-- Every public/ignored placement is a valid physical group for the actual guest byte
window. Each nonzero block demand in it is an eligible original row of the fixed block source. -/
theorem native_public_groups {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries) :
    let full := WriteStreams.fromEndpoints source.host target.host
    ∀ g ∈ entries.flatMap (Entry.publicGroups full), (g.Valid ∧ g.HonestCoordinates) ∧
      ∀ b ∈ directRequests g, (blockTable full).Spec b := by
  intro full g member
  obtain ⟨entry,inTape,group⟩ := List.mem_flatMap.mp member
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  rw [ordered] at inTape
  obtain ⟨⟨e,i⟩,indexed,emitted⟩ := List.mem_filterMap.mp inTape
  change position image source events readers e i = some entry at emitted
  have present := List.mk_mem_zipIdx_iff_getElem?.mp indexed
  have real := (native_position_active run readers present).1
  rw [emitted] at real
  cases e with
  | ordinary => contradiction
  | syscall call =>
    have write : call.rawCode = SyscallKind.write.code := of_decide_eq_true real.symm
    obtain ⟨current,_,cursor,_,len,buf,_,reached,_,stored,_,read,occurs,packet,dispatch,_⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans occurs)
    obtain ⟨_,_,_,_,atCurrent,observed,atStore,_,_,_,localOK,covered⟩ := native_destination_groups run present write
    cases Option.some.inj (reached.symm.trans atCurrent)
    cases Option.some.inj (read.symm.trans observed)
    cases Option.some.inj (stored.symm.trans atStore)
    unfold Entry.publicGroups at group
    split at group
    next => contradiction
    next no =>
      rw [packet,dispatch] at group
      rw [dispatch] at no
      have endTime := run.1.2.clock_at present reached
      have bounded := run.2.2.2.2.2.1
      change current.clock + 264 ≤ target.clock at endTime
      change target.clock < 2^48 at bounded
      rw [packet_eq (by omega) (paid_prefix run reached)] at group
      refine ⟨localOK g group,?_⟩
      intro b requested
      let route := WriteRoute.ofDescriptor call.arg1
      let earlier := WriteStreams.fromEndpoints source.host current.host
      by_cases key : (destinationKey route earlier).isSome
      · obtain ⟨k,has⟩ := Option.isSome_iff_exists.mp key
        have lookup := covered k has g group
        rcases List.mem_append.mp requested with left | right
        · split at left
          next on => exact (List.mem_singleton.mp left) ▸ ((blockTable full).contains_iff _).mp (lookup false on)
          next => contradiction
        · split at right
          next on => exact (List.mem_singleton.mp right) ▸ ((blockTable full).contains_iff _).mp (lookup true on)
          next => contradiction
      · have ignored : route = .ignored := by
          cases tag : WriteRoute.ofDescriptor call.arg1 <;> simp [route,tag,destinationKey,dispatchRow,dispatchColumns,routeFlags] at no key ⊢
        have zero : (effectSink route : F) = 0 := by rw [ignored]; rfl
        change g ∈ packetGroups _ _ _ (effectSink route : F) _ _ _ _ at group
        rw [zero] at group
        rw [ignored_silent group] at requested
        contradiction

/-- Occurrence-by-occurrence, groups receive the same clock, raw guest address and eight
decoded bytes as the physical word decoder for the collected packet. -/
theorem Entry.placementGroups_octets (full : WriteStreams) (e : Entry) :
    let header := e.dispatch.request.header
    (e.placementGroups full).map Group.octets =
      (effectRows (p := SP1Prime) (Address.toNat header.clock) header.descriptor.toBitVec64 header.address.toBitVec64
        e.packet.1 e.packet.2).2.map (WordRow.octets (256 : F)⁻¹) := by
  unfold Entry.placementGroups Entry.directGroups Entry.publicGroups
  by_cases direct : e.dispatch.flags.direct = 1
  · simp only [ite_eq_left direct,List.append_nil]
    exact packetGroups_octets ..
  · simp only [ite_eq_right direct,List.nil_append,fromPacket]
    exact packetGroups_octets ..

/-- Each original WRITE guest word yields exactly one row in the single chronological group table. -/
theorem placementGroups_length (full : WriteStreams) (entries : List Entry) :
    (entries.flatMap (Entry.placementGroups full)).length = WriteObservations.wordProbes (inputs entries).packets := by
  change _ = WriteObservations.wordProbes (entries.map Entry.packet)
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    simp only [List.flatMap_cons,List.length_append,List.map_cons,WriteObservations.wordProbes,List.sum_cons] at *
    rw [ih]
    congr 1
    unfold Entry.placementGroups Entry.directGroups Entry.publicGroups
    by_cases yes : entry.dispatch.flags.direct = 1 <;> simp [yes,fromPacket,packetGroups_length]

private theorem packet_plans (clk address length : Nat) (sink : F) (owner : fields 3 F) (buf : List (BitVec 64))
    (start : Nat) (destination : Bytes) {g : Group F} (member : g ∈ packetGroups clk address length sink owner buf start destination) :
    (planTable (p := SP1Prime)).Spec g.plan := by
  obtain ⟨⟨w,i⟩,_,rfl⟩ := List.mem_map.mp member
  let word := address / 8 + i
  have bounds := window_spec address length word
  apply (slicePlans_iff _).mpr
  exact ⟨_,_,_,bounds.1,bounds.2.1,Nat.mod_lt _ (by decide : 0 < 8),rfl⟩

/-- Every actual placement, including an empty selected interval, uses one of the fixed
verifier windows. The ordered packet determines the guest range and destination offset. -/
theorem Entry.placement_plan (e : Entry) (full : WriteStreams) {g : Group F} (member : g ∈ e.placementGroups full) :
    (planTable (p := SP1Prime)).Spec g.plan := by
  unfold Entry.placementGroups Entry.directGroups Entry.publicGroups at member
  by_cases direct : e.dispatch.flags.direct = 1 <;> simp only [direct,ite_true,ite_false,List.nil_append,List.append_nil] at member
  all_goals exact packet_plans _ _ _ _ _ _ _ _ member

end SP1Clean.WriteEffects.Witness
