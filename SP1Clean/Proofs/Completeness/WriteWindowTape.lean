import SP1Clean.Proofs.Completeness.WriteGroupRows

/-! # Grouped words from a successful WRITE cut

Each original guest word yields one row. The classifier selects its actual sink, including
ignored writes, and the payload bytes are obtained by executing the released read and dispatcher.
The owner is a routing identity; a separate chronological allocation assigns persistent pointers.
-/

namespace SP1Clean.WriteEffects
open Semantics Machine FormalModel.Shard TraceGen Soundness
open TraceGen.WriteObservations Soundness.Target

variable {p : Nat} [Fact p.Prime] [Fact (2^17 < p)]

/-- Destination tag used on the physical placement channel. Hooks address the consumed reply. -/
def effectSink : WriteRoute → Nat
  | .hook _ => 3
  | route => route.tag

private def observedOctets (clock word : Nat) (w : BitVec 64) : Octets (ZMod p) :=
  let row := WordRow.populate ⟨Address.ofNat (8*word),Address.ofNat clock,bitVecToWord w⟩
  row.octets (256 : ZMod p)⁻¹

private theorem observed_lane (clock word : Nat) (w : BitVec 64) (lane : Fin 8) :
    (observedOctets (p := p) clock word w).bytes[lane] = ((Soundness.wordBytes w)[lane].toNat : ZMod p) := by
  let read : WriteProbe.Read (ZMod p) := ⟨Address.ofNat (8*word),Address.ofNat clock,bitVecToWord w⟩
  let row := WordRow.populate read
  have valid : row.Valid := by
    apply WordRow.valid_of_decomp
    have small := isU64_bitVecToWord (p := p) w
    exact (U16toU8OperationSafe.spec_populate (small 0) (small 1) (small 2) (small 3) 1) rfl
  obtain ⟨bound,value⟩ := valid lane
  have exactByte := congrArg BitVec.toNat value
  change (row.octets _).bytes[lane].val % 256 = _ at exactByte
  rw [Nat.mod_eq_of_lt bound] at exactByte
  have decode : row.read.value.toBitVec64 = w := toBitVec64_bitVecToWord _
  rw [decode] at exactByte
  apply ZMod.val_injective p
  have hp : 2^17 < p := Fact.out
  rw [ZMod.val_natCast_of_lt (by have := (Soundness.wordBytes w)[lane].isLt; omega)]
  change (row.octets _).bytes[lane].val = _
  rw [exactByte]
  fin_cases lane <;> rfl

/-- Join the exact physical group inputs to a packet-local stream. The list order is the real
aligned read order; all full words are retained, even when a word contributes no selected bytes. -/
def packetGroups (clk address length : Nat) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (buffer : List (BitVec 64)) : List (Group (ZMod p)) :=
  let bytes := WriteObservations.payload buffer address length
  buffer.zipIdx.map fun (w,i) =>
    let word := address / 8 + i
    let (first,size) := window address length word
    Group.populate (observedOctets clk word w) sink owner first size (8*word+first-address) bytes

omit [Fact (2^17 < p)] in
theorem packetGroups_length (clk address length : Nat) (sink : ZMod p) (owner : fields 3 (ZMod p)) (buffer : List (BitVec 64)) :
    (packetGroups clk address length sink owner buffer).length = buffer.length := by simp [packetGroups]

omit [Fact (2^17 < p)] in
/-- The groups reuse the exact same physical input words as the released word decoder. -/
theorem packetGroups_octets (clk : Nat) (fd address length : BitVec 64) (sink : ZMod p) (owner : fields 3 (ZMod p))
    (buffer : List (BitVec 64)) :
    (packetGroups clk address.toNat length.toNat sink owner buffer).map (·.octets) =
      (effectRows (p := p) clk fd address length buffer).2.map (WordRow.octets (256 : ZMod p)⁻¹) := by
  simp only [packetGroups,effectRows,List.map_map]
  rfl

/-- All group circuit inputs are constructed from the packet itself. No per-byte hypotheses
or independent stream are needed, including a partial final block or a zero-length write. -/
theorem packetGroups_honest (clk address length : Nat) (sink : ZMod p) (owner : fields 3 (ZMod p)) (buffer : List (BitVec 64))
    (lower : 2^16 ≤ address) (upper : address+length ≤ 2^48) (count : buffer.length = wordCount address length) :
    ∀ group ∈ packetGroups clk address length sink owner buffer, group.Valid ∧ group.HonestCoordinates := by
  intro group member
  obtain ⟨⟨w,i⟩,atIndex,rfl⟩ := List.mem_map.mp member
  obtain ⟨inside,atWord⟩ := List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp atIndex)
  have wordBound : i < (address%8+length+7)/8 := by simpa only [count,wordCount] using inside
  let word := address / 8 + i
  let first := (window address length word).1
  let size := (window address length word).2
  let base := 8*word+first-address
  have geometry := window_spec address length word
  have startPositive : 0 < 8*word+first := by dsimp only [word]; omega
  have top : 8*word < 2^48 := by dsimp only [word]; omega
  have full : base+size ≤ length := by dsimp only [base,first,size,window,word]; omega
  change (Group.populate (observedOctets clk word w) sink owner first size base (WriteObservations.payload buffer address length)).Valid ∧ _
  apply Group.populate_valid _ _ _ _ _ _ word _ rfl geometry.1 geometry.2.1 startPositive top (by omega)
  · intro _ _
    rw [WriteObservations.payload_length count]
    exact full
  · intro slot _ used
    have small : first+slot.val < 8 := by have := geometry.2.1; change first+size ≤ 8 at this; omega
    have align : address%8+(base+slot.val) = i*8+(first+slot.val) := by
      dsimp only [base,first,word,window] at *
      omega
    have actual := payload_byte inside small (by omega : base+slot.val < length) align
    rw [actual,Option.getD_some,atWord]
    change (observedOctets (p := p) clk word w).bytes[(first+slot.val)%8] = ((Soundness.wordBytes w)[first+slot.val].toNat : ZMod p)
    simpa only [Fin.getElem_fin,Nat.mod_eq_of_lt small] using observed_lane (p := p) clk word w ⟨first+slot.val,small⟩

/-- The real admitted host event determines the group data, byte contents, route and complete
single-event effect. The chosen identity can be instantiated by the real allocation/dispatch
cursor; it has no influence on any authenticated data or state transition. -/
theorem groups_of_admissibleExecution {limits : ResourceLimits} {image : ProgramImage} {source target : ExecutionSnapshot}
    {events : List ExecutionEvent} (run : AdmissibleExecution limits p image source target events)
    {cut : Nat} {call : CoreSyscallEvent} (present : events[cut]? = some (.syscall call)) (write : call.rawCode = SyscallKind.write.code) :
    ∃ current next length buffer,
      WriteObservations.read? current.sail call = some (length,buffer) ∧
      executionTrajectory (policy p image) image.program source.realize events cut = some current ∧
      executionTrajectory (policy p image) image.program source.realize events (cut+1) = some next ∧
      let route := WriteRoute.ofDescriptor call.arg1
      let bytes := WriteObservations.payload buffer call.arg2.toNat length.toNat
      route.Effect current.host bytes next.host ∧
      ∀ owner : fields 3 (ZMod p), let groups := packetGroups current.clock call.arg2.toNat length.toNat (effectSink route : ZMod p) owner buffer
        groups.length = wordCount call.arg2.toNat length.toNat ∧
        groups.map (·.octets) = (effectRows (p := p) current.clock call.arg1 call.arg2 length buffer).2.map (WordRow.octets (256 : ZMod p)⁻¹) ∧
        ∀ r ∈ groups, r.Valid ∧ r.HonestCoordinates := by
  obtain ⟨current,next,frontier,length,buffer,pre,post,_,read,count,_,_,_,_,ran,_⟩ :=
    WriteObservations.of_admissibleExecution run present write
  obtain ⟨_,_,lower,upper,_,_⟩ := read?_eq_some_iff.mp read
  refine ⟨current,next,length,buffer,read,?_,?_,(WriteRoute.effect_iff ..).mpr ran,?_⟩
  · obtain ⟨s,f,seen,recovered,_⟩ := admissibleExecution_mixedAccessPrefix run cut
    rw [pre] at recovered
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj recovered)
    exact seen
  · obtain ⟨s,f,seen,recovered,_⟩ := admissibleExecution_mixedAccessPrefix run (cut+1)
    rw [post] at recovered
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj recovered)
    exact seen
  · intro owner
    exact ⟨(packetGroups_length ..).trans count,packetGroups_octets ..,packetGroups_honest _ _ _ _ _ _ lower upper count⟩

end SP1Clean.WriteEffects
