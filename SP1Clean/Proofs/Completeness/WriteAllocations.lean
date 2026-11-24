import SP1Clean.Proofs.Operations.HintQueuePrepend
import SP1Clean.Semantics.Host.HintQueueWordRecords
import SP1Clean.Semantics.Host.WriteEffects

/-! # Persistent records of the shared prepend compiler

The physical allocation order is the reverse of the logical hint prefix. This theorem
follows the same indexed row constructor used by direct WRITE and supplied hook replies.
-/

namespace SP1Clean.HintNodeAllocate
open Semantics HintQueue
variable {p : ℕ} [Fact p.Prime] [Fact (2^17 < p)]

/-- The generated row at each physical position authenticates the node and every padded word
at its permanent pointer. The incoming head can be below the allocation frontier. -/
theorem compilePrepend_records (clock : ℕ) (store : Store) (head : ℕ) (hints added : List Bytes)
    (rep : Represents store head hints) (space : store.size + added.length < 2^48) (i : Fin added.length) :
    let bytes := added.reverse[i.val]'(by simp)
    let pointer := store.size + i + 1
    let node := Node.mk bytes (if i.val = 0 then head else store.size + i)
    ∃ row, (compilePrepend (p := p) clock store head added)[i.val]? = some row ∧
      row.node = NodeRecord.encode pointer node ∧ Spec row ∧ row.node.Binds (prepend store head added).1 ∧
      ∀ word ∈ nodeWordRows (p := p) pointer bytes, word.Binds (prepend store head added).1 ∧ word.pointer = row.node.pointer := by
  let bytes := added.reverse[i.val]'(by simp)
  let state := prefixState (p := p) clock head store.size i
  let row := populate state bytes
  have chosen : added.reverse[i.val]? = some bytes := List.getElem?_eq_getElem (by simp)
  have atRow : (compilePrepend (p := p) clock store head added)[i.val]? = some row := by
    simp [compilePrepend,row,state,bytes]
  have read := node?_prepend_at store head added chosen
  have bounded : store.size + i.val + 1 < 2^48 := by have := i.isLt; omega
  have tailBound : (if i.val = 0 then head else store.size + i.val) < store.size + i.val + 1 := by
    have := rep.bound
    split <;> omega
  have record : row.node = NodeRecord.encode (store.size + i + 1)
      ⟨bytes, if i.val = 0 then head else store.size + i⟩ := by
    change NodeRecord.encode (Address.toNat (Address.ofNat (p := p) (store.size + i.val)) + 1)
      ⟨bytes,Address.toNat (Address.ofNat (p := p) (if i.val = 0 then head else store.size + i.val))⟩ = _
    rw [Address.toNat_ofNat _ (by omega),Address.toNat_ofNat _ (by omega)]
  refine ⟨row,atRow,record,compilePrepend_spec clock store head hints added rep space row (List.mem_of_getElem? atRow),
    record ▸ NodeRecord.encode_binds read bounded tailBound,?_⟩
  intro word member
  refine ⟨nodeWordRows_binds read bounded word member,?_⟩
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
  rw [record]
  rfl

end SP1Clean.HintNodeAllocate

namespace SP1Clean.WriteEffects
open Semantics HintQueue HintNodeAllocate
variable {p : ℕ} [Fact p.Prime] [Fact (2^17 < p)]

/-- Replaying the physical prepend rows yields the complete host effect's outgoing queue. -/
theorem allocate_effect {route : WriteRoute} {source target : HostState} {bytes : Bytes}
    (effect : route.Effect source bytes target) (clock : ℕ) (store : Store) (head : ℕ)
    (current : Represents store head source.io.hints) (fits : store.size + (route.allocations source bytes).length < 2^48) :
    let added := route.allocations source bytes
    let final := prepend store head added
    let outgoing := HostHintQueue.State.encode (p := p) clock final.2 final.1.size
    replayCursors (HostHintQueue.State.encode clock head store.size) (compilePrepend clock store head added) = some outgoing ∧
      outgoing.Binds final.1 target.io.hints :=
  ⟨compilePrepend_replay clock store head _ fits, effect.queue ▸ compilePrepend_binds clock store head _ _ current fits⟩

end SP1Clean.WriteEffects
