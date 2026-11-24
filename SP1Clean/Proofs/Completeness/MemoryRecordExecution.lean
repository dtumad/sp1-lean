import SP1Clean.Proofs.Completeness.MemoryHistoryValues

/-! # Handoffs from the actual Memory compiler

A filtered sequence at each register or RAM location consumes and produces its actual clock and
word. The canonical ledger's hand-off relation describes both the source and target frontiers.
-/

namespace SP1Clean.TraceGen.MemoryHistoryAccess

open Semantics LookupAccessList

private def endpoints (a : MemoryHistoryAccess) : (ℕ × Option (BitVec 64)) × (ℕ × Option (BitVec 64)) :=
  ((a.previous, some a.pulled), (a.current, some a.pushed))

/-- Each location consumes the incoming clock and word and hands exactly its outgoing record to
the next segment. Repeated accesses retain their order in the original transfer tape. -/
def Transfers (before after : AccessFrontier) (source target : LocationValues) (records : List MemoryHistoryAccess) : Prop :=
  ∀ loc, IsHandoffChain (before loc, source loc) ((memoryHistoryAt records loc).map endpoints) (after loc, target loc)

/-- An empty segment preserves its entire current image. -/
theorem Transfers.nil (f : AccessFrontier) (s : LocationValues) : Transfers f f s s [] := fun _ => rfl

/-- Consecutive segments compose at exactly the same intermediate clock and value frontier. -/
theorem Transfers.append {first middle last : AccessFrontier} {source next target : LocationValues}
    {left right : List MemoryHistoryAccess} (h : Transfers first middle source next left)
    (k : Transfers middle last next target right) : Transfers first last source target (left ++ right) := by
  intro loc
  simpa only [memoryHistoryAt, List.filter_append, List.map_append] using (h loc).append (k loc)

private theorem singleton (f : AccessFrontier) (s : LocationValues) (a : MemoryHistoryAccess)
    (clock : a.previous = f a.loc) (read : some a.pulled = s a.loc) :
    Transfers f (Function.update f a.loc a.current) s (Function.update s a.loc (some a.pushed)) [a] := by
  intro loc
  by_cases same : a.loc = loc
  · subst loc
    simp [memoryHistoryAt, IsHandoffChain, endpoints, read, clock]
  · simp [memoryHistoryAt, same, IsHandoffChain, Function.update_of_ne (Ne.symm same)]

private theorem transfers_tail {f g : AccessFrontier} {s t : LocationValues} {a : MemoryHistoryAccess}
    {rest : List MemoryHistoryAccess} (h : Transfers f g s t (a :: rest)) :
    Transfers (Function.update f a.loc a.current) g (Function.update s a.loc (some a.pushed)) t rest := by
  intro loc
  have valid := h loc
  by_cases same : a.loc = loc
  · subst loc
    simp only [memoryHistoryAt, List.filter_cons, decide_true, ↓reduceIte, List.map_cons, IsHandoffChain] at valid
    simpa only [Function.update_self, memoryHistoryAt, endpoints] using valid.2
  · simp only [memoryHistoryAt, List.filter_cons, same, decide_false, Bool.false_eq_true, ite_false] at valid
    simpa only [Function.update_of_ne (Ne.symm same), memoryHistoryAt] using valid

/-- The posted value image of a valid sequence is exactly the final image in its hand-offs. -/
theorem Transfers.post_eq {f g : AccessFrontier} {s t : LocationValues} {records : List MemoryHistoryAccess}
    (h : Transfers f g s t records) : post s records = t := by
  induction records generalizing f s with
  | nil => exact funext fun loc => congrArg Prod.snd (show (f loc, s loc) = (g loc, t loc) from h loc)
  | cons a records ih => exact ih (transfers_tail h)

/-- Distinct single-location postings compose from genuine endpoint records. A location outside
the batch keeps its original clock and value. -/
theorem transfers_disjoint {f g : AccessFrontier} {s t : LocationValues} {records : List MemoryHistoryAccess}
    (unique : (records.map MemoryHistoryAccess.loc).Nodup)
    (atRecord : ∀ a ∈ records,
      a.previous = f a.loc ∧ some a.pulled = s a.loc ∧ a.current = g a.loc ∧ some a.pushed = t a.loc)
    (framed : ∀ loc, (∀ a ∈ records, a.loc ≠ loc) → (f loc, s loc) = (g loc, t loc)) :
    Transfers f g s t records := by
  induction records generalizing f s with
  | nil => exact fun loc => framed loc (by simp)
  | cons a rest ih =>
    obtain ⟨fresh, others⟩ := List.nodup_cons.mp unique
    have values := atRecord a List.mem_cons_self
    have later : ∀ r ∈ rest, r.loc ≠ a.loc := fun r mem eq => fresh (List.mem_map.mpr ⟨r, mem, eq⟩)
    apply (singleton f s a values.1 values.2.1).append (right := rest)
    apply ih others
    · intro r mem
      simpa only [Function.update_of_ne (later r mem)] using atRecord r (List.mem_cons_of_mem a mem)
    · intro loc absent
      by_cases here : loc = a.loc
      · subst loc; simp only [Function.update_self]; exact Prod.ext values.2.2.1 values.2.2.2
      · simp only [Function.update_of_ne here]
        apply framed
        simpa only [List.mem_cons, forall_eq_or_imp] using And.intro (Ne.symm here) absent

private theorem scheduled_transfer (f : AccessFrontier) (s : LocationValues) (base : ℕ) (touch : PlannedTouch)
    (read : s touch.loc = some touch.pulled) :
    Transfers f (advanceFrontier f base touch) s (Function.update s touch.loc (some touch.pushed))
      (ofScheduledAccess base (scheduleAccess f base touch)) := by
  let posted := ofStamped base (scheduleAccess f base touch).stamped
  cases emitted : memoryBumpEvent? f base touch with
  | none =>
    rw [ofScheduledAccess_noBump (by exact emitted)]
    exact singleton f s posted (by simp [posted, ofStamped, scheduleAccess, scheduledPrevious, emitted]) read.symm
  | some event =>
    rw [ofScheduledAccess_someBump (by exact emitted)]
    obtain ⟨index, located, _, rfl⟩ := memoryBumpEvent?_shape emitted
    let refresh := ofMemoryBump ⟨index.toNat, touch.pulled.toNat, f touch.loc, base + 1⟩
    have place : refresh.loc = touch.loc := by simp [refresh, ofMemoryBump, located]
    have old : refresh.pulled = touch.pulled := by simp [refresh, ofMemoryBump]
    have keep : refresh.pushed = touch.pulled := old
    have bump := singleton f s refresh (by rw [place]; rfl) (by rw [place, old, read])
    have same : Function.update s touch.loc (some touch.pulled) = s := Function.update_eq_self_iff.mpr read.symm
    rw [place, keep, same] at bump
    have instr := singleton (Function.update f touch.loc (base + 1)) s posted
      (by change scheduledPrevious f base touch = (Function.update f touch.loc (base + 1)) touch.loc
          simp [scheduledPrevious, emitted]) read.symm
    have combined := bump.append instr
    change Transfers f (Function.update (Function.update f touch.loc (base + 1)) touch.loc (touch.recordTime base)) s
      (Function.update s touch.loc (some touch.pushed)) ([refresh] ++ [posted]) at combined
    rw [Function.update_idem] at combined
    exact combined

/-- Success of a canonical access plan authenticates every prior and posted clock and word on the
expanded stream, including register refreshes and later operand roles aliasing an earlier one. -/
theorem transfers_of_schedule {plan : InstructionAccessPlan} {s t : LocationValues}
    (valid : plan.RunsFrom s t) (f : AccessFrontier) (base : ℕ) :
    Transfers f (advancePlan f base plan) s t (ofAccessSchedule base (scheduleAccessPlan f base plan)) := by
  induction plan generalizing s f with
  | nil => cases InstructionAccessPlan.runsFrom_nil_iff.mp valid; exact Transfers.nil f _
  | cons touch later ih =>
    obtain ⟨read, rest⟩ := InstructionAccessPlan.runsFrom_cons_iff.mp valid
    rw [scheduleAccessPlan_cons, ofAccessSchedule_cons]
    exact (scheduled_transfer f s base touch read).append (ih rest _)

private theorem history_links {l : MemLoc} {a : MemoryHistoryAccess} {rest : List MemoryHistoryAccess}
    {first last : ℕ × Option (BitVec 64)}
    (places : ∀ r ∈ a :: rest, r.loc = l)
    (walk : IsHandoffChain first ((a :: rest).map endpoints) last) :
    (a.previous, some a.pulled) = first ∧ List.IsChain Continues (a :: rest) := by
  induction rest generalizing a first with
  | nil => exact ⟨walk.1, List.isChain_singleton _⟩
  | cons b more ih =>
    obtain ⟨head, tail⟩ := walk
    obtain ⟨bond, linked⟩ := ih (fun r occurs => places r (List.mem_cons_of_mem a occurs)) tail
    refine ⟨head, List.isChain_cons_cons.mpr ⟨?_, linked⟩⟩
    exact ⟨(places b (by simp)).trans (places a List.mem_cons_self).symm, congrArg Prod.fst bond,
      Option.some.inj (congrArg Prod.snd bond)⟩

private theorem history_start {loc : MemLoc} {records : List MemoryHistoryAccess} (nonempty : records ≠ [])
    (places : ∀ r ∈ records, r.loc = loc) {start finish : ℕ × Option (BitVec 64)}
    (run : IsHandoffChain start (records.map endpoints) finish) :
    (records.head nonempty).previous = start.1 ∧ List.IsChain Continues records := by
  cases records with
  | nil => exact False.elim (nonempty rfl)
  | cons a rest =>
    obtain ⟨prior, chain⟩ := history_links places run
    exact ⟨congrArg Prod.fst prior, chain⟩

/-- Threaded hand-offs from genesis prove the record chronology required by the existing
per-location boundary and ordered Memory ledger constructors. -/
theorem Transfers.chronology {final : AccessFrontier} {source target : LocationValues} {records : List MemoryHistoryAccess}
    (valid : Transfers AccessFrontier.initial final source target records) : MemoryRecordChronology records := by
  intro history member
  obtain ⟨item, _, rfl⟩ := List.mem_map.mp member
  obtain ⟨loc, touched⟩ := item
  exact history_start (memoryHistoryAt_ne_nil_of_mem touched)
    (fun _ mem => of_decide_eq_true (List.mem_filter.mp mem).2) (valid loc)

end SP1Clean.TraceGen.MemoryHistoryAccess
