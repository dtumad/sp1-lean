import SP1Clean.Proofs.Completeness.WriteCollectedGroups
import SP1Clean.Proofs.Completeness.WriteBufferBatch

/-! # Routing one chronological collection through the WRITE classifier and word decoder

The located buffer rows and the dispatcher come from the same successful WRITE. The original clock, operands, and every
observed aligned word determine the receiver inputs, including reads shared by distinct packets.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen Soundness.Target WriteAllocation
private abbrev F := ZMod SP1Prime

/-- All aligned words of this actual entry, including boundary words of a partial slice. -/
def Entry.decoderRows (entry : Entry) : List (WordRow F) :=
  let header := entry.dispatch.request.header
  (effectRows (p := SP1Prime) (Address.toNat header.clock) header.descriptor.toBitVec64 header.address.toBitVec64
    entry.packet.1 entry.packet.2).2

/-- The actual header is classified once; all decoder inputs use exactly the original physical reads in order. -/
def MatchesBuffer (buffer : WriteBuffer.PacketRows F) (entry : Entry) : Prop :=
  entry.dispatch.request = Request.populate buffer.span.header ∧ entry.dispatch.request.Valid ∧
    entry.decoderRows = buffer.steps.map (fun step => WordRow.populate step.read)

/-- All native buffer packets match the respective dispatcher and word inputs at their genuine execution cuts. -/
theorem native_collected_effects {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (emitted : native? image source events readers = some entries) :
    List.Forall₂ MatchesBuffer (WriteBuffer.packetRows events (inputs entries).packets) entries := by
  obtain ⟨rows,found,located,_⟩ := native_inputs run readers
  obtain rfl := Option.some.inj (emitted.symm.trans found)
  rw [located]
  apply WriteBuffer.packetRows_related (fun (e,i) => position image source events readers e i) Entry.packet
  · intro e i used
    exact (native_position_active run readers used).1
  intro call cut entry used write atCut
  obtain ⟨current,_,_,_,len,buf,row,reached,_,_,_,_,seen,packet,dispatch,_⟩ := native_position run readers used write
  have same : entry = row := Option.some.inj (atCut.symm.trans seen)
  subst entry
  obtain ⟨other,_,_,atOther,_,step,_,_,_,bounded,_⟩ := admissibleExecution_syscall_from_prefix run used
  have same : other = current := Option.some.inj (atOther.symm.trans reached)
  subst other
  have clock : call.clock = current.clock := by
    cases step with
    | syscall success =>
      obtain ⟨_,_,_,_,_,_,_,rfl⟩ := HostState.step_observations success
      rfl
  let h := WriteBuffer.headerOfCall (p := SP1Prime) current.clock call len
  have header : row.dispatch.request = Request.populate h := by rw [dispatch]; rfl
  have cleanClock : Address.toNat h.clock = current.clock := Address.toNat_ofNat _ (by omega)
  have cleanAddress : h.address.toBitVec64 = call.arg2 := toBitVec64_bitVecToWord _
  unfold MatchesBuffer
  rw [header,packet]
  refine ⟨?_,Request.populate_valid _ (isU64_bitVecToWord _),?_⟩
  · simp only [WriteBuffer.makePacketRows,clock]
    rfl
  · unfold Entry.decoderRows
    rw [header,packet]
    change (effectRows (p := SP1Prime) (Address.toNat h.clock) _ h.address.toBitVec64 len buf).2 = _
    rw [cleanClock,cleanAddress]
    simp only [effectRows,WriteBuffer.makePacketRows,WriteBuffer.wordSteps,List.zipIdx_map,List.map_map,clock]
    rfl

/-- The private word decoder always receives its actual four bounded limbs and their canonical low bytes. -/
theorem Entry.decoderRows_honest (entry : Entry) (data : ProverData F) (hint : ProverHint F) :
    ∀ r ∈ entry.decoderRows, wordCircuit.ProverAssumptions r data hint := by
  intro r mem
  obtain ⟨⟨_,_⟩,_,rfl⟩ := List.mem_map.mp mem
  exact WordRow.populate_honest _ (isU64_bitVecToWord _) data hint

/-- Ordered classifier headers, aligned words and word octets agree across the three actual collector projections. -/
theorem effect_projections {batch : List (WriteBuffer.PacketRows F)} {entries : List Entry}
    (matched : List.Forall₂ MatchesBuffer batch entries) (streams : WriteStreams) :
    (batch.map (fun p => p.span.header)) = (entries.map (fun e => e.dispatch.request.header)) ∧
    ((batch.flatMap WriteBuffer.PacketRows.steps).map WriteBuffer.Step.read) = ((entries.flatMap Entry.decoderRows).map WordRow.read) ∧
    ((entries.flatMap Entry.decoderRows).map (WordRow.octets (256 : F)⁻¹)) = ((entries.flatMap (Entry.placementGroups streams)).map Group.octets) ∧
    ∀ e ∈ entries, e.dispatch.request.Valid := by
  induction matched with
  | nil => simp
  | cons head _ ih =>
    obtain ⟨request,valid,words⟩ := head
    obtain ⟨headers,reads,octets,allValid⟩ := ih
    refine ⟨?_,?_,?_,?_⟩
    · simp only [List.map_cons,request,Request.populate,headers]
    · simp only [List.flatMap_cons,List.map_append,reads,words,List.map_map]
      rfl
    · simp only [List.flatMap_cons,List.map_append,octets,Entry.placementGroups_octets,Entry.decoderRows]
    · exact List.forall_mem_cons.mpr ⟨valid,allValid⟩

end SP1Clean.WriteEffects.Witness
