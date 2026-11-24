import SP1Clean.Export.WriteDispatchWalk

/-! # Unique WRITE dispatchers and their own complete placement walks -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- The public stream walk assigns a unique incoming ECALL clock to each physical
dispatcher, including nonallocating and zero-length calls. -/
theorem native_dispatch_clocks (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((physicalDispatches (observed w)).map (fun d => Address.toNat d.request.header.clock)).Nodup := by
  obtain ⟨_,path,all,_,times,_,_⟩ := native_dispatch_chronology w ok fit raw
  exact (all.map (fun d : Dispatch F => Address.toNat d.request.header.clock)).nodup_iff.mp (times.imp Nat.ne_of_lt)

/-- Every active dispatcher is valid, and a route requesting allocation supplies a physical allocating row. -/
theorem physical_dispatch_valid (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (mem : d ∈ physicalDispatches (observed w)) :
    d.Valid ∧ (d.flags.direct+d.flags.hook = 1 → d ∈ allocatingDispatches (observed w)) := by
  obtain ⟨r,kept,rfl⟩ := List.mem_map.mp mem
  obtain ⟨present,one⟩ := List.mem_filter.mp kept
  have enabled := of_decide_eq_true one
  have v := (native_dispatch_input_facts w ok fit raw r present).2 enabled
  refine ⟨v,fun gate => List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨present,?_⟩,rfl⟩⟩
  apply decide_eq_true
  simp only [ticketGate,enabled,gate,one_mul]

/-- An allocating ticket comes from an active physical dispatcher. -/
theorem allocating_dispatch_active (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (mem : d ∈ allocatingDispatches (observed w)) :
    d ∈ physicalDispatches (observed w) := by
  have gate := ((native_allocation_tickets w ok fit raw).2 d mem).2
  obtain ⟨r,kept,rfl⟩ := List.mem_map.mp mem
  obtain ⟨present,one⟩ := List.mem_filter.mp kept
  have field : ticketGate r = 1 := of_decide_eq_true one
  have active : r.2 = 1 := by simpa only [ticketGate,gate,mul_one] using field
  exact List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨present,decide_eq_true active⟩,rfl⟩

/-- The checked dispatcher selects tag 14 exactly for the one-hot direct route. -/
theorem direct_shape {d : Dispatch F} (v : d.Valid) :
    (d.flags.direct = 1 ↔ d.flags.sink = 14) ∧
    (d.flags.direct = 1 → d.flags = ⟨0,0,0,0,1⟩) := by
  rw [v.1]
  have cases := flagsFor_choices d.request.route
  simp only [List.mem_cons,List.mem_nil_iff,or_false,Prod.mk.injEq] at cases
  rcases cases with h | h | h | h | h | h <;> rw [h.1] <;>
    norm_num [DispatchFlags.sink,DispatchFlags.hook,SP1Prime]
  all_goals
    intro contradiction
    have impossible := congrArg ZMod.val contradiction
    revert impossible
    decide

private theorem walk_key {groups : List (WriteEffects.Group F)} {start finish : Placement F}
    (walk : Walk.IsWalk (fun g : WriteEffects.Group F => (g.previous,g.next)) start finish groups) :
    finish.clock = start.clock ∧ finish.sink = start.sink ∧ finish.owner = start.owner := by
  induction groups generalizing start with
  | nil => change start = finish at walk; simp [walk]
  | cons g tail ih =>
    obtain ⟨same,later⟩ := walk
    change g.previous = start at same
    subst start
    exact ih (start := g.next) later

/-- Every actual dispatcher has its own complete placement walk to the finish it declared.
The full position multiset and incoming ECALL clock identify the owner of every endpoint. -/
theorem native_dispatch_placement (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w)) :
    ∃ groups : List (WriteEffects.Group F),
      Walk.IsWalk (fun g : WriteEffects.Group F => (g.previous,g.next)) (d.start d.flags) (d.finish d.flags) groups ∧
      ∀ g ∈ groups,g ∈ placementSteps (observed w) := by
  let seen := observed w
  let calls := physicalDispatches seen
  obtain ⟨paths,paired,ends,all⟩ := native_placement_walks w ok fit raw
  have appears : d ∈ (calls.zip paths).map Prod.fst := by rw [List.map_fst_zip paired.length_eq.le]; exact md
  obtain ⟨⟨actual,path⟩,both,e⟩ := List.mem_map.mp appears
  change actual = d at e
  subst actual
  have walk := (List.forall₂_iff_zip.mp paired).2 both
  have inPath := (List.of_mem_zip both).2
  have terminal := ends.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) inPath)
  obtain ⟨other,otherMem,endEq⟩ := List.mem_map.mp terminal
  have key := walk_key walk
  rw [← endEq] at key
  have sameTime : other.request.header.clock = d.request.header.clock := key.1
  have same := List.inj_on_of_nodup_map (native_dispatch_clocks w ok fit raw) otherMem md (congrArg Address.toNat sameTime)
  subst other
  exact ⟨path.1,endEq.symm ▸ walk,fun g m => all.mem_iff.mp (List.mem_flatMap.mpr ⟨path,inPath,m⟩)⟩

end SP1Clean.Export.WriteObservationAssembly
