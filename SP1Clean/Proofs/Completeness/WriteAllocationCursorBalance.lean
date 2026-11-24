import SP1Clean.Proofs.Completeness.WriteAllocationCursorTables
import SP1Clean.Proofs.Completeness.WriteAllocationStoredWords
import SP1Clean.Soundness.RankedGrounding

/-! # Closing allocation cursor channels over the constructed physical tables

A call row and its fresh-node rows traverse the ordered prepend. Each node seed and its
own padded words form a second traversal ending on the first partially occupied word.
Both equalities survive batching and Clean's independent demand padding.
-/

namespace SP1Clean.WriteAllocation
open Air.Flat Semantics HintQueue Soundness

private abbrev F := ZMod SP1Prime

/-- The actual fresh-node constructor emits one occupied input per allocated buffer. -/
theorem Batch.steps_length (batch : Batch) (clock : Nat) (store : Store) (head : Nat)
    (readers : NodeRecord F → F) : (batch.steps clock store head readers).length = batch.buffers.length := by
  simp [Batch.steps, HintNodeAllocate.compilePrepend_length]

private theorem indexed_walk {A V : Type} (edge : A → V × V) (rows : List A) (pt : Nat → V)
    (ends : ∀ i : Fin rows.length, edge rows[i] = (pt i, pt (i.val+1))) :
    Walk.IsWalk edge (pt 0) (pt rows.length) rows := by
  induction rows generalizing pt with
  | nil => rfl
  | cons x xs ih =>
    have first := ends ⟨0, by simp⟩
    change edge x = (pt 0, pt 1) at first
    have tail := ih (fun n => pt (n+1)) (fun i => ends ⟨i.val+1, Nat.succ_lt_succ i.isLt⟩)
    exact ⟨congrArg Prod.fst first, (congrArg Prod.snd first).symm ▸ tail⟩

/-- Stored node publications connect the first and terminal call cursors in allocation order.
This includes a hook with no returned buffers, where the first cursor already equals the last. -/
theorem Batch.steps_walk (batch : Batch) (clock : Nat) (before : Store × Nat) (after : Store)
    (issued : batch.Publishes clock before after) (readers : NodeRecord F → F) :
    Walk.IsWalk (fun r : Step F => (r.before,r.after))
      (batch.cursorAt clock before.2 before.1.size 0) (batch.cursorAt clock before.2 before.1.size batch.buffers.length)
      (batch.steps clock before.1 before.2 readers) := by
  have size := batch.steps_length clock before.1 before.2 readers
  rw [← size]
  apply indexed_walk
  intro i
  obtain ⟨row,found,_,first,last,_⟩ := issued readers ⟨i.val,size ▸ i.isLt⟩
  rw [List.getElem?_eq_getElem i.isLt] at found
  have value : (batch.steps clock before.1 before.2 readers)[i] = row := Option.some.inj found
  rw [value,first,last]

private theorem one_batch (r : Open F) (steps : List (Step F)) (msg : Array F)
    (walk : Walk.IsWalk (fun n : Step F => (n.before,n.after)) r.first r.last steps) :
    balanceOf (openCursors (r,1)) msg + balanceOf (steps.flatMap (fun n => stepCursors (n,1))) msg = 0 := by
  let edge := fun n : Step F => (n.before,n.after)
  have ends := RankedGrounding.endpointBalanced_of_isWalk edge walk
  have paired : (r.first :: steps.map Step.after).Perm (r.last :: steps.map Step.before) := by
    simpa only [RankedGrounding.EndpointBalanced,Multiset.map_coe,Multiset.cons_coe,Multiset.coe_eq_coe,edge] using ends
  have balance := (cursorChannel.transitionLedger_balanced_iff r.first r.last steps edge).mpr paired
  have unit : ∀ i ∈ cursorChannel.transitionLedger r.first r.last steps edge, IsBool i.mult := by
    intro i member
    have perm := (cursorChannel.transitionLedger_perm r.first r.last steps edge).mem_iff.mp member
    rcases List.mem_append.mp perm with put | get
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp put
      exact Or.inr rfl
    · obtain ⟨_,_,rfl⟩ := List.mem_map.mp get
      exact Or.inr rfl
  rw [← balanceOf_append]
  exact balance.logUp_of_isBool unit msg

/-- The actual call and node tables close their shared cursor at every payload. All batches
share one independently padded table of each kind; equal cursors may occur repeatedly. -/
theorem batch_cursor {A : Type} (batch : List A) (call : A → Open F) (nodes : A → List (Step F))
    (walk : ∀ a ∈ batch, Walk.IsWalk (fun n : Step F => (n.before,n.after)) (call a).first (call a).last (nodes a))
    (data : ProverData F) (hc hn) :
    LogUpBalanced ((openTable (batch.map call) data hc).interactionsWith cursorChannel.toRaw ++
      (stepTable (batch.flatMap nodes) data hn).interactionsWith cursorChannel.toRaw) := by
  intro msg
  rw [balanceOf_append,openTable_cursors,stepTable_cursors,WitnessGeneration.guardedRows_balanceOf,WitnessGeneration.guardedRows_balanceOf]
  · clear hc hn
    induction batch with
    | nil => simp [balanceOf]
    | cons a as ih =>
      have head := one_batch (call a) (nodes a) msg (walk a List.mem_cons_self)
      have tail := ih (fun x mem => walk x (List.mem_cons_of_mem _ mem))
      simp only [List.map_cons,List.flatMap_cons,List.flatMap_append,balanceOf_append]
      linear_combination head + tail
  · simp only [stepCursors,balanceOf_cons]
    simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]
    exact ite_self 0
  · simp only [openCursors,balanceOf_cons]
    simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]
    exact ite_self 0

namespace Words

/-- A unit-weight contribution of a typed cursor to one raw message sum. -/
private def atMessage (c : Cursor F) (msg : Array F) : F :=
  if (cursorChannel.pushedValue c).msg = msg then 1 else 0

private theorem word_delta (r : Row F) (msg : Array F) :
    balanceOf (wordCursors (r,1)) msg = r.payload.more * atMessage r.next msg - atMessage r.prior msg := by
  by_cases prior : (cursorChannel.pushedValue r.prior).msg = msg <;>
    by_cases next : (cursorChannel.pushedValue r.next).msg = msg <;>
    simp_all [atMessage, wordCursors, balanceOf, Channel.pushedValue,
      Channel.pushedIfValue, Channel.pulledIfValue, Interaction.signedMult]
  ring

private theorem seed_credit (c : Contents F) (msg : Array F) :
    balanceOf (seedCursors (c,1)) msg = atMessage (start c) msg := by
  simp only [seedCursors,balanceOf_cons]
  by_cases same : (toElements (start c)).toArray = msg <;>
    simp [atMessage,balanceOf,Channel.pushedValue,Channel.pushedIfValue,Interaction.signedMult,same]

private theorem one_walk (c : Contents F) (bytes : Bytes) (br wr : Nat → F) (msg : Array F)
    (length : c.length = Address.ofNat bytes.length) :
    balanceOf (seedCursors (c,1)) msg + balanceOf ((walk c bytes br wr).flatMap (fun r => wordCursors (r,1))) msg = 0 := by
  let row := fun i => populate c bytes i (br i) (wr i)
  let n := wordCount bytes
  let credit := fun i => if i < n then atMessage (row i).prior msg else 0
  have live : 0 < n := Nat.zero_lt_succ _
  have step (i : Nat) (inside : i < n) :
      balanceOf (wordCursors (row i,1)) msg = credit (i+1) - credit i := by
    have flag := populate_last (p := SP1Prime) bytes inside
    change 1 - (row i).payload.more = _ at flag
    have next : (row i).next = (row (i+1)).prior := rfl
    rw [word_delta,next]
    by_cases terminal : i+1 = n
    · rw [ite_eq_left terminal] at flag
      have off : (row i).payload.more = 0 := by linear_combination -flag
      simp [credit,inside,terminal,off]
    · rw [ite_eq_right terminal] at flag
      have on : (row i).payload.more = 1 := by linear_combination -flag
      simp [credit,inside,show i+1 < n by omega,on]
  have upto (k : Nat) (bound : k ≤ n) :
      balanceOf ((List.range k).flatMap (fun i => wordCursors (row i,1))) msg = credit k - credit 0 := by
    induction k with
    | zero => simp [balanceOf]
    | succ k ih =>
      rw [List.range_succ,List.flatMap_append,List.flatMap_singleton,balanceOf_append,ih (by omega),step k (by omega)]
      abel
  have exactRows : walk c bytes br wr = (List.range n).map row := by
    apply List.ext_getElem
    · simp [walk,n]
    · intro i hi hj
      simp [walk,row]
  have closed := upto n (le_refl _)
  have first : (row 0).prior = start c := populate_start c bytes _ _ length
  rw [seed_credit,exactRows,List.flatMap_map]
  rw [closed]
  simp [credit,live,first]

/-- Seed and padded word tables close their private cursor for every allocated node.
Read multiplicities may depend on both node and position. Empty and aligned nodes include
their canonical last word. There is one demand padding operation per physical table. -/
theorem batch_cursor {A : Type} (nodes : List A) (contents : A → Contents F) (bytes : A → Bytes)
    (br wr : A → Nat → F) (lengths : ∀ a ∈ nodes, (contents a).length = Address.ofNat (bytes a).length)
    (data : ProverData F) (hs hw) :
    LogUpBalanced ((seedTable (nodes.map contents) data hs).interactionsWith cursorChannel.toRaw ++
      (wordTable (nodes.flatMap fun a => walk (contents a) (bytes a) (br a) (wr a)) data hw).interactionsWith cursorChannel.toRaw) := by
  intro msg
  rw [balanceOf_append,seedTable_cursors,wordTable_cursors,WitnessGeneration.guardedRows_balanceOf,WitnessGeneration.guardedRows_balanceOf]
  · clear hs hw
    induction nodes with
    | nil => simp [balanceOf]
    | cons a rest ih =>
      have head := one_walk (contents a) (bytes a) (br a) (wr a) msg (lengths a List.mem_cons_self)
      have tail := ih (fun x mem => lengths x (List.mem_cons_of_mem _ mem))
      simp only [List.map_cons,List.flatMap_cons,List.flatMap_append,balanceOf_append]
      linear_combination head + tail
  · simp only [wordCursors,balanceOf_cons]
    simp [Channel.pulledIfValue,Channel.pushedIfValue,Interaction.signedMult,balanceOf]
  · simp only [seedCursors,balanceOf_cons]
    simp [Channel.pushedIfValue,Interaction.signedMult,balanceOf]
    exact ite_self 0

end Words

end SP1Clean.WriteAllocation
