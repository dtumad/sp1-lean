import SP1Clean.Proofs.Operations.WriteAllocation
import SP1Clean.Proofs.Operations.HintQueuePrepend
import SP1Clean.Proofs.Operations.ClockOrderPopulate
import SP1Clean.Math.SP1Field

/-! # Compiling the data authorized by one allocating WRITE

The header names the actual persistent frontier. Each node carries the byte length and
identity from the existing prepend constructor. A hook's input bytes remain distinct from
the buffers returned by its supplied reply.
-/

namespace SP1Clean.WriteAllocation
open Semantics HintQueue Soundness.Target

private abbrev F := ZMod SP1Prime

/-- The two kinds of allocation authority, with the exact guest buffer or supplied hook reply. -/
inductive Batch where
  /-- One fresh node containing the bytes read from guest memory. -/
  | direct (bytes : Bytes)
  /-- The actual ordinal, guest input size and ordered list of buffers in the consumed reply. -/
  | hook (reply inputSize : Nat) (returned : List Bytes)

/-- Buffers prepended to the logical queue, in the order observed by HINT_READ. -/
def Batch.buffers : Batch → List Bytes
  | .direct bytes => [bytes]
  | .hook _ _ returned => returned

/-- Circuit ticket supplied by the authenticated chronological dispatcher. -/
def Batch.ticket (batch : Batch) (clock frontier : Nat) : WriteEffects.QueueTicket F :=
  match batch with
  | .direct bytes => ⟨Address.ofNat clock,1,Address.ofNat (frontier+1),Address.ofNat bytes.length,0⟩
  | .hook reply input returned => ⟨Address.ofNat clock,0,Address.ofNat reply,Address.ofNat input,Address.ofNat returned.length⟩

/-- Publicly supplied stream identity or private guest bytes of the fresh direct node. -/
def Batch.source (batch : Batch) (frontier : Nat) : Source F :=
  match batch with
  | .direct bytes => ⟨1,Address.ofNat (frontier+1),Address.ofNat bytes.length⟩
  | .hook reply _ _ => ⟨0,Address.ofNat reply,0⟩

private def parts (clk : Nat) : ClockParts F := ClockParts.split (clk / 2^24 : Nat) (clk % 2^24 : Nat)

private theorem parts_spec (clk : Nat) (fit : clk < 2^48) :
    (parts clk).Bounded ∧ (parts clk).high24 = (clk / 2^24 : Nat) ∧ (parts clk).low24 = (clk % 2^24 : Nat) ∧
    (parts clk).address = Address.ofNat clk := by
  have field : 2^24 < SP1Prime := by decide
  have hi : ((clk / 2^24 : Nat) : F).val = clk / 2^24 := ZMod.val_natCast_of_lt (by omega)
  have lo : ((clk % 2^24 : Nat) : F).val = clk % 2^24 := ZMod.val_natCast_of_lt (by omega)
  obtain ⟨b,high,low⟩ := ClockParts.split_spec ((clk/2^24 : Nat) : F) ((clk%2^24 : Nat) : F)
    (by rw [hi]; omega) (by rw [lo]; omega)
  refine ⟨b,high,low,?_⟩
  have time := (parts clk).time b
  change (parts clk).high24 = _ at high
  change (parts clk).low24 = _ at low
  rw [high,low,clkNat,hi,lo] at time
  have exactTime : Address.toNat (parts clk).address = clk := by omega
  exact ((Address.ofNat_toNat ((parts clk).address_bounded b)).symm).trans (congrArg Address.ofNat exactTime)

/-- The actual incoming and outgoing private cursors of one allocating WRITE. -/
def Batch.openRow (batch : Batch) (prior clk : Nat) (store : Store) (head : Nat) : Open F :=
  let next := prepend store head batch.buffers
  ⟨batch.ticket clk store.size,parts clk,HostHintQueue.State.encode prior head store.size,Address.ofNat next.2,Address.ofNat next.1.size⟩

/-- One physical node input from the existing checked prepend constructor. -/
def Batch.step (batch : Batch) (count i : Nat) (node : HintNodeAllocate.Inputs F) (readers : NodeRecord F → F) : Step F :=
  ⟨node,(batch.source 0).direct,(match batch with | .direct _ => 0 | .hook reply _ _ => Address.ofNat reply),
    Address.ofNat (count - i),Address.ofNat (count - (i + 1)),readers node.node⟩

/-- Physical order is reverse logical reply order. Each permanently allocated node appears once. -/
def Batch.steps (batch : Batch) (clk : Nat) (store : Store) (head : Nat) (readers : NodeRecord F → F) : List (Step F) :=
  let count := batch.buffers.length
  (HintNodeAllocate.compilePrepend clk store head batch.buffers).zipIdx.map fun (node,i) => batch.step count i node readers

/-- Shared cursor after allocating precisely the last `i` logical buffers. -/
def Batch.cursorAt (batch : Batch) (clk head frontier i : Nat) : Cursor F :=
  ⟨batch.source frontier, Address.ofNat (batch.buffers.length - i), HintNodeAllocate.prefixState clk head frontier i⟩

private theorem three (x : fields 3 F) : #v[x[0],x[1],x[2]] = x := by
  ext i inside
  interval_cases i <;> rfl

private theorem source_fields (batch : Batch) (prior clk : Nat) (store : Store) (head : Nat) :
    (batch.openRow prior clk store head).source = batch.source store.size ∧
    (batch.openRow prior clk store head).count = Address.ofNat batch.buffers.length := by
  cases batch <;> simp [Batch.openRow,Batch.ticket,Batch.source,Batch.buffers,Open.source,Open.count,scale,Address.ofNat]
  rfl

/-- Clock order, the exact initial chain position and the exact semantic post-call queue. -/
theorem Batch.openRow_valid (batch : Batch) (prior clk : Nat) (store : Store) (head : Nat)
    (ordered : prior < clk) (bounded : clk < 2^48) :
    let row := batch.openRow prior clk store head
    row.Valid ∧ row.first = batch.cursorAt clk head store.size 0 ∧
    row.last = batch.cursorAt clk head store.size batch.buffers.length ∧
    row.outgoing = HostHintQueue.State.encode clk (prepend store head batch.buffers).2 (prepend store head batch.buffers).1.size := by
  obtain ⟨b,hi,lo,addr⟩ := parts_spec clk bounded
  obtain ⟨src,count⟩ := source_fields batch prior clk store head
  let row := batch.openRow prior clk store head
  have clock : row.order = ClockOrder.encode prior clk := by
    simp [row,Batch.openRow,Open.order,HostHintQueue.State.encode,ClockOrder.encode,hi,lo]
  have post : row.outgoing = HostHintQueue.State.encode clk (prepend store head batch.buffers).2 (prepend store head batch.buffers).1.size := by
    simp [row,Batch.openRow,Open.outgoing,HostHintQueue.State.encode,hi,lo]
  refine ⟨⟨?_,b,?_,clock ▸ ClockOrder.encode_spec prior clk bounded ordered⟩,?_,?_,post⟩
  · cases batch <;> simp [Batch.openRow,Batch.ticket,IsBool]
  · cases batch <;> exact addr.symm
  · change Cursor.mk _ _ _ = _
    rw [src,count]
    simp [Batch.cursorAt,Batch.openRow,Open.outgoing,HintNodeAllocate.prefixState,HostHintQueue.State.encode,hi,lo]
  · have last : (prepend store head batch.buffers).2 = if batch.buffers.length = 0 then head else store.size + batch.buffers.length := by
      cases batch.buffers with
      | nil => rfl
      | cons bytes tail => simp [prepend,prepend_size,Nat.add_assoc]
    change Cursor.mk _ _ row.outgoing = _
    rw [post,src]
    simp [Batch.cursorAt,HintNodeAllocate.prefixState,prepend_size,last,Address.ofNat_zero]
    rfl

private theorem lengthWord (bytes : Bytes) (small : bytes.length < 2^48) :
    bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 bytes.length) = Address.asWord (Address.ofNat bytes.length) := by
  simp [bitVecToWord, Address.asWord, Address.ofNat, BitVec.extractLsb'_toNat, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow]
  rw [Nat.div_eq_of_lt (by omega : bytes.length < 281474976710656)]
  rfl

private theorem step_length {r : Step F} {a : fields 3 F} (packed : r.node.node.length = Address.asWord a) : r.length = a := by
  simp only [Step.length,packed,Address.asWord,circuit_norm,three]

private theorem direct_source {r : Step F} (on : r.direct = 1) :
    r.source = ⟨1,r.node.node.pointer,r.length⟩ := by
  simp [Step.source,on,WriteEffects.threeLimbs,scale,three]

private theorem hook_source {r : Step F} (off : r.direct = 0) :
    r.source = ⟨0,r.reply,0⟩ := by
  simp [Step.source,off,WriteEffects.threeLimbs,scale,three]
  rfl

private theorem node_next {clock head frontier i : Nat} {bytes : Bytes}
    (ptr : (HintNodeAllocate.populate (HintNodeAllocate.prefixState (p := SP1Prime) clock head frontier i) bytes).node.pointer =
      Address.ofNat (frontier + i+1)) :
    (HintNodeAllocate.populate (HintNodeAllocate.prefixState (p := SP1Prime) clock head frontier i) bytes).next =
      HintNodeAllocate.prefixState clock head frontier (i+1) := by
  unfold HintNodeAllocate.Inputs.next
  rw [ptr]
  simp [HintNodeAllocate.populate,HintNodeAllocate.prefixState,HostHintQueue.State.encode,Nat.add_assoc]

/-- Every live row is the actual authorized node. Its exact before/after cursors
and the issued contents record identify the same pointer, byte count and hook index. -/
theorem Batch.steps_at (batch : Batch) (clk : Nat) (store : Store) (head : Nat) (hints : List Bytes)
    (rep : Represents store head hints) (space : store.size + batch.buffers.length < 2^48)
    (sizes : ∀ b ∈ batch.buffers, b.length < 2^48) (readers : NodeRecord F → F) (i : Fin batch.buffers.length) :
    let bytes := batch.buffers.reverse[i.val]'(by simp)
    ∃ r, (batch.steps clk store head readers)[i.val]? = some r ∧ r.Valid ∧
      r.before = batch.cursorAt clk head store.size i ∧ r.after = batch.cursorAt clk head store.size (i + 1 : Nat) ∧
      r.contents.pointer = Address.ofNat (store.size + i + 1) ∧ r.contents.length = Address.ofNat bytes.length ∧
      r.contents.index = Address.ofNat (batch.buffers.length - (i + 1 : Nat)) ∧
      r.readers = readers r.node.node := by
  let buffers := batch.buffers
  have inside : i.val < buffers.reverse.length := by simp [buffers]
  let bytes := buffers.reverse[i.val]'inside
  let state := HintNodeAllocate.prefixState (p := SP1Prime) clk head store.size i
  let node := HintNodeAllocate.populate state bytes
  let r := batch.step batch.buffers.length i node readers
  have inputAt : (HintNodeAllocate.compilePrepend (p := SP1Prime) clk store head buffers)[i.val]? = some node := by
    simp [HintNodeAllocate.compilePrepend,List.getElem?_map,List.getElem?_zipIdx,List.getElem?_eq_getElem inside,node,state,bytes]
  have got : (batch.steps clk store head readers)[i.val]? = some r := by
    simp [Batch.steps,List.getElem?_map,List.getElem?_zipIdx,r,show batch.buffers = buffers from rfl,inputAt]
  have good := HintNodeAllocate.compilePrepend_spec (p := SP1Prime) clk store head hints buffers rep space node (List.mem_of_getElem? inputAt)
  have word := lengthWord bytes (sizes bytes (List.mem_reverse.mp (List.getElem_mem inside)))
  have bounded : store.size + i.val < 2^48 := by have := i.isLt; omega
  have ptr : node.node.pointer = Address.ofNat (store.size + i + 1) := by
    change Address.ofNat (Address.toNat (Address.ofNat (p := SP1Prime) (store.size + i.val)) + 1) = _
    rw [Address.toNat_ofNat _ bounded]
  have len : r.length = Address.ofNat bytes.length := step_length (r := r) word
  have next : node.next = HintNodeAllocate.prefixState clk head store.size (i.val + 1) := node_next ptr
  have src : r.source = batch.source store.size := by
    cases batch with
    | hook reply input returned => exact hook_source (r := r) rfl
    | direct data =>
      have ix : i.val = 0 := by have := i.isLt; change i.val < 1 at this; omega
      have value : bytes = data := by simp [bytes,buffers,Batch.buffers,ix]
      have on : r.direct = 1 := rfl
      have ptr' : r.node.node.pointer = Address.ofNat (store.size + 1) := calc
        _ = node.node.pointer := rfl
        _ = _ := ptr.trans (by rw [ix,Nat.add_zero])
      rw [direct_source on,ptr',len,value]
      rfl
  refine ⟨r,got,⟨?_,good,?_,?_⟩,?_,?_,?_,len,rfl,rfl⟩
  · cases batch <;> simp [r,Batch.step,Batch.source,IsBool]
  · change (bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 bytes.length))[3] = 0
    rw [word]; rfl
  · have eq : batch.buffers.length - (i.val+1) + 1 = batch.buffers.length - i.val := by have := i.isLt; omega
    have sum := AddressSum.spec_ofNat (p := SP1Prime) (batch.buffers.length - (i.val+1)) 1 (by omega)
    rw [eq,show Address.ofNat (p := SP1Prime) 1 = #v[1,0,0] by decide] at sum
    exact sum
  · change Cursor.mk r.source _ _ = _
    rw [src]; rfl
  · change Cursor.mk r.source _ node.next = _
    rw [src,next]; rfl
  · exact ptr

end SP1Clean.WriteAllocation
