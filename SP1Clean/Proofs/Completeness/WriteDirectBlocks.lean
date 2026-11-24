import SP1Clean.Proofs.Completeness.WriteReturnedBlocks
import SP1Clean.Proofs.Completeness.WriteBlockLedgers

/-! # Funding the private placement of each direct WRITE block

The chronological entry determines the guest words, clock, address and fresh allocation
pointer. Each enabled side of a physical placement belongs to an occupied word of that
same permanent node. A crossing between two guest windows can read a block twice.
-/

namespace SP1Clean.WriteEffects.Witness
open Semantics Machine FormalModel.Shard TraceGen WriteAllocation HintQueue
open scoped Classical
private abbrev F := ZMod SP1Prime

/-- Private demand groups built from the packet and dispatch columns already collected.
An empty direct hint retains any aligned guest read required by the packet, while hooks
and other descriptors contribute no private block demand. -/
def Entry.directGroups (e : Entry) : List (Group F) :=
  if e.dispatch.flags.direct = 1 then
    let header := e.dispatch.request.header
    let address := header.address.toBitVec64.toNat
    let bytes := WriteObservations.payload e.packet.2 address e.packet.1.toNat
    packetGroups (Address.toNat header.clock) address e.packet.1.toNat 14 e.dispatch.pointer e.packet.2 0 bytes
  else []

private theorem occupied {g : Group F} {bytes : Bytes} {c : Contents F} {clk addr len : Nat}
    {buffer : List (BitVec 64)} (count : buffer.length = WriteObservations.wordCount addr len)
    (size : bytes.length = len)
    (member : g ∈ packetGroups clk addr len 14 c.pointer buffer 0 bytes) (right : Bool)
    (active : (if right then g.rightGate else g.leftGate) = 1) :
    ∃ j : Fin (wordCount bytes), 8*j.val < bytes.length ∧
      ∀ br wr : F, (Words.populate c bytes j.val br wr).direct = g.block right := by
  obtain ⟨⟨w,i⟩,atWord,rfl⟩ := List.mem_map.mp member
  have inside := (List.getElem?_eq_some_iff.mp (List.mk_mem_zipIdx_iff_getElem?.mp atWord)).1
  have last : i < (addr%8+len+7)/8 := by simpa only [count,WriteObservations.wordCount] using inside
  let word : Nat := addr / 8 + i
  let first := (window addr len word).1
  let used := (window addr len word).2
  let base := 0+(8*word+first-addr)
  have within : base+used ≤ bytes.length := by dsimp only [word,first,used,base,window]; omega
  let j : Nat := if right then base/8+1 else base/8
  have live : 8*j < bytes.length := by
    cases right with
    | false =>
      have nonempty : used ≠ 0 := by
        intro empty
        change (Group.populate _ _ _ first used base bytes).leftGate = 1 at active
        simp [Group.leftGate,Group.populate,SlicePlan.ofNat,empty] at active
      change 8 * (base / 8) < _
      omega
    | true =>
      have cross : 8 < used + base % 8 := by
        by_contra no
        change (Group.populate _ _ _ first used base bytes).rightGate = 1 at active
        simp [Group.rightGate,Group.populate,SlicePlan.ofNat,no] at active
      change 8 * (base / 8 + 1) < _
      omega
  refine ⟨⟨j,by unfold wordCount; omega⟩,live,?_⟩
  intro br wr
  exact Words.populate_direct_group c bytes br wr _ first used base right

private theorem direct_node {bytes : Bytes} {clock prior : Nat} {before : Store × Nat} {after : Store}
    (readers : Readers) (stored : (Batch.direct bytes).Publishes clock before after) :
    ∃ node ∈ ((Batch.direct bytes).rows prior clock before readers).nodes,
      node.step.contents.pointer = Address.ofNat (before.1.size+1) ∧ node.step.contents.direct = 1 ∧
      node.words = (nodeRows readers node.step bytes).words := by
  obtain ⟨node,atNode,_,first,_,ptr,_,words,_⟩ :=
    (Batch.direct bytes).rows_at prior clock before after stored readers ⟨0,by simp [Batch.buffers]⟩
  have mode := congrArg (fun s : Cursor F => s.source.direct) first
  exact ⟨node,List.mem_of_getElem? atNode,ptr,mode,words⟩

private theorem in_direct_batch {bytes : Bytes} {clock prior : Nat} {before : Store × Nat} {after : Store}
    (readers : Readers) (stored : (Batch.direct bytes).Publishes clock before after)
    {clk addr len : Nat} {buf : List (BitVec 64)} (count : buf.length = WriteObservations.wordCount addr len)
    (size : bytes.length = len) {g : Group F}
    (member : g ∈ packetGroups clk addr len 14 (Address.ofNat (before.1.size+1)) buf 0 bytes)
    (right : Bool) (enabled : (if right then g.rightGate else g.leftGate) = 1) :
    ∃ node ∈ ((Batch.direct bytes).rows prior clock before readers).nodes, ∃ row ∈ node.words,
      row.directGate = 1 ∧ row.direct = g.block right ∧ row.blockReads = readers.blocks (g.block right) := by
  obtain ⟨node,contains,ptr,mode,words⟩ := direct_node (prior := prior) readers stored
  rw [← ptr] at member
  obtain ⟨j,live,same⟩ := occupied count size member right enabled
  let plain := Words.populate node.step.contents bytes j.val 0 0
  let r := Words.populate node.step.contents bytes j.val (readers.blocks plain.direct) (readers.words plain.word)
  refine ⟨node,contains,r,?_,?_,same _ _,?_⟩
  · rw [words]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  · have pos : 0 < Words.extent bytes j := by dsimp only [Words.extent]; omega
    simp only [r,Words.populate,Words.Row.directGate,Words.Payload.populate,Vector.getElem_ofFn,mode,one_mul]
    exact ite_eq_left pos
  · exact congrArg readers.blocks (same 0 0)

/-- Each live private placement in the chronological compilation is funded by an occupied
word at that cut's fresh pointer. The supplied multiplicity is indexed by the entire block. -/
theorem native_direct_blocks {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)
    {g : Group F} (member : g ∈ entries.flatMap Entry.directGroups) (right : Bool)
    (enabled : (if right then g.rightGate else g.leftGate) = 1) :
    ∃ row ∈ (inputs entries).words, row.directGate = 1 ∧ row.direct = g.block right ∧
      row.blockReads = readers.blocks (g.block right) := by
  obtain ⟨entry,inTape,group⟩ := List.mem_flatMap.mp member
  obtain ⟨actual,built,ordered,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  have original := inTape
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
    obtain ⟨current,_,before,after,len,buf,_,_,_,_,_,read,occurs,packet,dispatch,_,_,cert⟩ := native_position run readers present write
    cases Option.some.inj (emitted.symm.trans occurs)
    have count := (WriteObservations.read?_eq_some_iff.mp read).2.2.2.2.1
    let bytes := WriteObservations.payload buf call.arg2.toNat len.toNat
    have size : bytes.length = len.toNat := WriteObservations.payload_length count
    have direct : entry.dispatch.flags.direct = 1 := by
      by_contra no
      simp [Entry.directGroups,no] at group
    have mode : WriteRoute.ofDescriptor call.arg1 = .hint := by
      rw [dispatch] at direct
      cases route : WriteRoute.ofDescriptor call.arg1 <;> simp [dispatchRow,dispatchColumns,route,routeFlags] at direct ⊢
    have store := cert (.direct bytes) (by simp [mode,batchFor,batchAt,bytes])
    rw [Entry.directGroups,ite_eq_left direct,packet,dispatch] at group
    change g ∈ packetGroups _ (Soundness.Target.bitVecToWord (p := SP1Prime) call.arg2).toBitVec64.toNat len.toNat
      14 (Address.ofNat (before.1.size+1)) buf 0 (WriteObservations.payload buf
        (Soundness.Target.bitVecToWord (p := SP1Prime) call.arg2).toBitVec64.toNat len.toNat) at group
    simp only [Soundness.Target.toBitVec64_bitVecToWord] at group
    obtain ⟨node,contains,row,found,live,same,funding⟩ := in_direct_batch (prior := (events.take i).foldl advanceQueueClock 0)
      readers store.publishes count size group right enabled
    refine ⟨row,List.mem_flatMap.mpr ⟨node,List.mem_flatMap.mpr ⟨_,List.mem_filterMap.mpr ⟨entry,original,store.rows⟩,contains⟩,found⟩,live,same,funding⟩

end SP1Clean.WriteEffects.Witness
