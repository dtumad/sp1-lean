import SP1Clean.Proofs.Operations.WriteMetadataRows
import SP1Clean.Soundness.RankedGrounding

/-! # Absolute reply ordinals of a chronological WRITE dispatcher walk -/

namespace SP1Clean.WriteEffects
open Soundness Semantics
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq

/-- The stream clock reaches the call's incoming clock then advances by exactly one. -/
theorem Dispatch.Valid.stream_time {d : Dispatch F} (v : d.Valid) :
    Address.toNat d.previous.clock ≤ Address.toNat d.request.header.clock ∧
      Address.toNat (d.next d.flags).clock = Address.toNat d.request.header.clock + 1 := by
  obtain ⟨_,_,_,_,_,_,time,step,_⟩ := v
  have timeEq := time.2.2.2
  have stepEq := step.2.2.2
  change Address.toNat d.request.header.clock = Address.toNat d.previous.clock + _ at timeEq
  change Address.toNat d.nextClock = Address.toNat d.request.header.clock + Address.toNat (#v[1,0,0] : fields 3 F) at stepEq
  exact ⟨by omega,by rw [show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at stepEq; exact stepEq⟩

/-- Selecting a hook forces every special route flag to zero. -/
theorem Dispatch.Valid.hook_flags {d : Dispatch F} (v : d.Valid) (hook : d.flags.hook = 1) :
    d.flags = ⟨0,0,0,0,0⟩ := by
  have choices := flagsFor_choices d.request.route
  rw [← v.1,hook] at choices
  simpa only [List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq,one_ne_zero,and_false,false_or,and_true] using choices

/-- The checked dispatcher advances the natural reply cursor once exactly on a hook. -/
theorem Dispatch.Valid.reply_step {d : Dispatch F} (v : d.Valid) :
    Address.toNat (d.next d.flags).replies = Address.toNat d.previous.replies + (if d.flags.hook = 1 then 1 else 0) := by
  obtain hook | hook := v.allocation_gates.1
  · have same : (d.next d.flags).replies = d.previous.replies := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> simp [Dispatch.next,hook,threeLimbs,circuit_norm]
    simp [same,hook]
  · have shape := v.hook_flags hook
    have prev : d.baseCounter = d.previous.replies := by
      rw [v.2.2.2.2.1]
      apply Vector.ext
      intro i hi
      interval_cases i <;> simp [Dispatch.oldCounter,Dispatch.outputPosition,shape,DispatchFlags.hook,threeLimbs,circuit_norm]
    have add : d.delta = #v[1,0,0] := by
      rw [v.2.2.2.2.2.1,shape]
      simp [Dispatch.increment,DispatchFlags.hook,circuit_norm]
    have next : (d.next d.flags).replies = d.nextCounter := by
      apply Vector.ext
      intro i hi
      interval_cases i <;> simp [Dispatch.next,hook,threeLimbs,circuit_norm]
    have eq := v.2.2.2.2.2.2.2.2.2.2.2.2.2.2
    change Address.toNat d.nextCounter = Address.toNat d.baseCounter + Address.toNat d.delta at eq
    rw [prev,add,show Address.toNat (#v[1,0,0] : fields 3 F) = 1 by decide] at eq
    simpa only [next,hook,ite_true] using eq

/-- The incoming clock increases along the entire walk, including calls with an empty
payload and all nonallocating descriptors. -/
theorem dispatch_walk_order {start stop : StreamCursor F} {path : List (Dispatch F)}
    (walk : Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) start stop path)
    (valid : ∀ d ∈ path,d.Valid) :
    (path.map (fun d => Address.toNat d.request.header.clock)).Pairwise (· < ·) := by
  let edge := fun d : Dispatch F => (d.previous,d.next d.flags)
  have later := RankedGrounding.targetRanks_pairwise_of_isWalk edge (fun c : StreamCursor F => Address.toNat c.clock) walk (by
    intro d m
    obtain ⟨before,after⟩ := (valid d m).stream_time
    change Address.toNat d.previous.clock < Address.toNat (d.next d.flags).clock
    omega)
  rw [List.pairwise_map] at later ⊢
  apply later.imp_of_mem
  intro a b ma mb lt
  obtain ⟨_,aa⟩ := (valid a ma).stream_time
  obtain ⟨_,bb⟩ := (valid b mb).stream_time
  change Address.toNat (a.next a.flags).clock < Address.toNat (b.next b.flags).clock at lt
  omega

/-- The terminal cursor counts every hook in this walk. -/
theorem dispatch_walk_total {start stop : StreamCursor F} {path : List (Dispatch F)}
    (walk : Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) start stop path)
    (valid : ∀ d ∈ path,d.Valid) :
    Address.toNat stop.replies = Address.toNat start.replies + path.countP (fun d => decide (d.flags.hook = 1)) := by
  induction path generalizing start with
  | nil => change start = stop at walk; simp [walk]
  | cons d ds ih =>
    obtain ⟨first,rest⟩ := walk
    change d.previous = start at first
    subst start
    have fromTail := ih rest (fun x m => valid x (List.mem_cons_of_mem _ m))
    change Address.toNat stop.replies = Address.toNat (d.next d.flags).replies + _ at fromTail
    rw [(valid d List.mem_cons_self).reply_step] at fromTail
    by_cases hook : d.flags.hook = 1 <;> simpa [List.countP_cons,hook,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using fromTail

/-- The reply cursor before every occurrence counts all and only earlier hook calls. -/
theorem dispatch_walk_ordinals {start stop : StreamCursor F} {path : List (Dispatch F)}
    (walk : Walk.IsWalk (fun d : Dispatch F => (d.previous,d.next d.flags)) start stop path)
    (valid : ∀ d ∈ path,d.Valid) (i : Fin path.length) :
    Address.toNat path[i.val].previous.replies = Address.toNat start.replies +
      (path.take i.val).countP (fun d => decide (d.flags.hook = 1)) := by
  induction path generalizing start with
  | nil => exact Fin.elim0 i
  | cons d ds ih =>
    obtain ⟨first,rest⟩ := walk
    change d.previous = start at first
    subst start
    rcases i with ⟨i,hi⟩
    cases i with
    | zero => simp
    | succ i =>
      have h : i < ds.length := Nat.lt_of_succ_lt_succ hi
      have tailValue := ih rest (fun d m => valid d (List.mem_cons_of_mem _ m)) ⟨i,h⟩
      change Address.toNat ds[i].previous.replies = Address.toNat (d.next d.flags).replies + _ at tailValue
      rw [(valid d List.mem_cons_self).reply_step] at tailValue
      simp only [List.getElem_cons_succ,List.take_succ_cons,List.countP_cons]
      by_cases hook : d.flags.hook = 1 <;> simpa [hook,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tailValue

/-- Each consumed hook contributes its own metadata, so the checked inventory also bounds the reply count. -/
theorem hooks_lt_of_inventory {streams : WriteStreams} (valid : inventoryOK streams = true) : streams.hooks.length < 2 ^ 48 := by
  let records := fun (x : HookReply × Nat) => [Query.descriptor x.2,.returnCount x.2] ++
    byteQueries (.request x.2) x.1.request.input ++ x.1.hints.zipIdx.flatMap (fun (bytes,h) => byteQueries (.returned x.2 h) bytes)
  have lower (xs : List (HookReply × Nat)) : xs.length ≤ (xs.flatMap records).length := by
    induction xs with
    | nil => exact Nat.zero_le _
    | cons x xs ih =>
      simp only [List.length_cons,List.flatMap_cons,List.length_append] at *
      have two : 2 ≤ (records x).length := by simp [records]
      omega
  have validCount := ((inventoryOK_iff streams).mp valid).1
  have count : (queries streams).length = (byteQueries .stdout streams.stdout ++ byteQueries .stderr streams.stderr ++
      byteQueries .publicOutput streams.publicOutput ++ streams.hooks.zipIdx.flatMap records).length := rfl
  have minimum := lower streams.hooks.zipIdx
  rw [List.length_zipIdx] at minimum
  rw [count,List.length_append] at validCount
  omega

end SP1Clean.WriteEffects
