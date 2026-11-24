import SP1Clean.Proofs.Completeness.WriteAllocationBatch
import SP1Clean.Proofs.Completeness.WriteAllocationWordRows

/-! # Immutable publications from fresh WRITE allocations

Every allocated pointer names the actual stored guest or returned bytes. The node and every
padded physical word retain their bindings across all later persistent store extensions.
-/

namespace SP1Clean.WriteAllocation

open Semantics HintQueue

private abbrev F := ZMod SP1Prime

/-- The actual generated node and padded word messages name the same immutable allocation. -/
def Batch.Publishes (batch : Batch) (clock : Nat) (before : Store × Nat) (after : Store) : Prop :=
  ∀ (readers : NodeRecord F → F) (i : Fin batch.buffers.length),
    let bytes := batch.buffers.reverse[i.val]'(by simp)
    ∃ r, (batch.steps clock before.1 before.2 readers)[i.val]? = some r ∧ r.Valid ∧
      r.before = batch.cursorAt clock before.2 before.1.size i ∧
      r.after = batch.cursorAt clock before.2 before.1.size (i + 1 : Nat) ∧
      r.contents.pointer = Address.ofNat (before.1.size + i + 1) ∧
      r.contents.length = Address.ofNat bytes.length ∧ r.readers = readers r.node.node ∧
      ∀ later, Extends after later →
        r.node.node.Binds later ∧ ∀ j < wordCount bytes, ∀ br wr,
          (Words.populate r.contents bytes j br wr).word.Binds later

/-- The fresh-node and padded-word constructors produce records that bind the exact persistent store. -/
theorem Batch.publishes_prepend (batch : Batch) (clock : Nat) (store : Store) (head : Nat) (hints : List Bytes)
    (rep : Represents store head hints) (space : store.size + batch.buffers.length < 2^48)
    (sizes : ∀ b ∈ batch.buffers, b.length < 2^48) :
    batch.Publishes clock (store,head) (prepend store head batch.buffers).1 := by
  intro readers i
  dsimp only
  let bytes := batch.buffers.reverse[i.val]'(by simp)
  let tail := if i.val = 0 then head else store.size + i.val
  have actual : batch.buffers.reverse[i.val]? = some bytes := List.getElem?_eq_getElem (by simp)
  have read : node? (prepend store head batch.buffers).1 (store.size + i + 1) = some ⟨bytes,tail⟩ :=
    node?_prepend_at store head batch.buffers actual
  obtain ⟨r,atRow,valid,first,last,ptr,len,_,count,record⟩ := batch.steps_at clock store head hints rep space sizes readers i
  refine ⟨r,atRow,valid,first,last,ptr,len,count,?_⟩
  intro later extension
  have inLater := extension _ _ read
  have bound : store.size + i.val + 1 < 2^48 := by have := i.isLt; omega
  have desc : tail < store.size + i.val + 1 := by
    have := rep.bound
    dsimp [tail]
    split <;> omega
  refine ⟨record ▸ NodeRecord.encode_binds inLater bound desc,?_⟩
  intro j within br wr
  rw [Words.populate_word _ _ _ br wr (ptr ▸ Address.bounded_ofNat _) within,ptr,Address.toNat_ofNat _ bound]
  change j < wordCount bytes at within
  have small := sizes bytes (List.mem_reverse.mp (List.mem_of_getElem? actual))
  exact WordRecord.encode_binds inLater bound j within (by unfold wordCount at within; omega)

end SP1Clean.WriteAllocation
