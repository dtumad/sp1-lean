import SP1Clean.Proofs.Operations.HintNodeWords
import SP1Clean.Semantics.Host.WriteEffects

/-! # Persistent node and word construction for WRITE effects

A direct hint contributes its observed payload. A hook contributes the supplied reply's list
in reverse allocation order, so the first returned buffer becomes the next visible queue head.
Every intermediate node retains its complete padded words after later allocations.
-/

namespace SP1Clean.WriteEffects
open Semantics Semantics.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2^17 < p)]

/-- Raw allocation inputs paired with precisely the bytes inhabiting their new node. -/
abbrev Allocation (p : Nat) := HintNodeAllocate.Inputs (ZMod p) × Bytes

/-- Prepend buffers back-to-front using the actual preceding allocation row. -/
def allocate (before : HostHintQueue.State (ZMod p)) : List Bytes → List (Allocation p) × HostHintQueue.State (ZMod p)
  | [] => ([], before)
  | bytes :: rest =>
    let old := allocate before rest
    let row := HintNodeAllocate.populate old.2 bytes
    (old.1 ++ [(row, bytes)], row.next)

/-- Authenticated metadata, full padded word payload and fresh identity survive in the resulting store. -/
def Allocation.Binds (a : Allocation p) (store : Store) : Prop :=
  HintNodeAllocate.Spec a.1 ∧ a.1.node.Binds store ∧
    ∀ record ∈ nodeWordRows (p := p) (Address.toNat a.1.node.pointer) a.2,
      record.Binds store ∧ record.pointer = a.1.node.pointer

omit [Fact (2^17 < p)] in
private theorem Allocation.Binds.extend {a : Allocation p} {old new : Store} (bound : a.Binds old)
    (grow : Extends old new) : a.Binds new := by
  refine ⟨bound.1, bound.2.1.extend grow, ?_⟩
  intro row member
  obtain ⟨meaning, pointer⟩ := bound.2.2 row member
  exact ⟨meaning.extend grow, pointer⟩

omit [Fact (2^17 < p)] in
theorem allocate_bytes (previous : HostHintQueue.State (ZMod p)) (added : List Bytes) :
    ((allocate previous added).1.map Prod.snd) = added.reverse := by
  induction added with
  | nil => rfl
  | cons first rest ih => simp [allocate, ih]

/-- Each physical row and word authenticates its own permanent position in the same final store. -/
theorem allocate_binds (previous : HostHintQueue.State (ZMod p)) (store : Store) (hints added : List Bytes)
    (current : previous.Binds store hints) (fits : store.size + added.length < 2^48) :
    let final := prepend store (Address.toNat previous.head) added
    let rows := allocate previous added
    rows.2.Binds final.1 (added ++ hints) ∧ Address.toNat rows.2.head = final.2 ∧
      ∀ a ∈ rows.1, Allocation.Binds a final.1 := by
  induction added with
  | nil => exact ⟨current, rfl, by simp [allocate]⟩
  | cons bytes rest ih =>
    let old := prepend store (Address.toNat previous.head) rest
    let batch := allocate previous rest
    have fits' : store.size + rest.length < 2^48 := by simp only [List.length_cons] at fits; omega
    obtain ⟨represented, head, earlier⟩ := ih fits'
    change batch.2.Binds old.1 (rest ++ hints) at represented
    change Address.toNat batch.2.head = old.2 at head
    let row := HintNodeAllocate.populate batch.2 bytes
    have capacity : old.1.size + 1 < 2^48 := by
      change (prepend store _ rest).1.size + 1 < _
      rw [prepend_size]
      simp only [List.length_cons] at fits
      omega
    have valid := HintNodeAllocate.populate_spec batch.2 bytes old.1 _ represented capacity
    obtain ⟨next, node, words, grows⟩ := HintNodeAllocate.populate_contents batch.2 bytes old.1 _ represented capacity
    change row.next.Binds (old.1.push ⟨bytes, Address.toNat batch.2.head⟩) _ at next
    rw [head] at next node words grows
    refine ⟨next, ?_, ?_⟩
    · change Address.toNat row.node.pointer = old.1.size + 1
      exact HintNodeAllocate.identity_of_spec row valid old.1 _ represented
    · intro a member
      change a ∈ batch.1 ++ [(row, bytes)] at member
      rcases List.mem_append.mp member with prior | fresh
      · exact (earlier a prior).extend grows
      · obtain rfl := List.mem_singleton.mp fresh
        exact ⟨valid, node, words⟩

/-- Apply the actual descriptor's allocations, including the matched hook's empty or multiple hints. -/
theorem allocate_effect {route : WriteRoute} {source target : HostState} {bytes : Bytes}
    (effect : route.Effect source bytes target) (previous : HostHintQueue.State (ZMod p))
    (store : Store) (current : previous.Binds store source.io.hints)
    (fits : store.size + (route.allocations source bytes).length < 2^48) :
    let added := route.allocations source bytes
    let final := prepend store (Address.toNat previous.head) added
    let rows := allocate previous added
    rows.2.Binds final.1 target.io.hints ∧
      rows.1.map Prod.snd = added.reverse ∧ ∀ a ∈ rows.1, Allocation.Binds a final.1 := by
  obtain ⟨cursor, _, bound⟩ := allocate_binds previous store source.io.hints _ current fits
  exact ⟨effect.queue ▸ cursor, allocate_bytes .., bound⟩

end SP1Clean.WriteEffects
