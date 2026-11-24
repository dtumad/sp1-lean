import SP1Clean.Export.WritePlacementWalks

/-! # Unique direct WRITE dispatchers and their own complete placement walks -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteAllocation WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot}

/-- Complete ticket multiplicities and strictly ordered global queue clocks rule out any
duplicate allocating dispatcher at the same incoming ECALL clock. -/
theorem native_dispatch_clocks (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((allocatingDispatches (observed w)).map (fun d => Address.toNat d.request.header.clock)).Nodup := by
  let seen := observed w
  let cs := (allocationInputs seen).1
  have clock : cs.map (fun c => Address.toNat c.ticket.clock) = cs.map (fun c => HostQueueOrder.time c.outgoing) := by
    apply List.map_congr_left
    intro c mem
    have v := allocation_header_valid seen ((observed_constraints w).mp ok) c mem
    rw [v.2.2.1]
    exact c.timestamp.time v.2.1
  have clocks := (native_allocation_tickets w ok fit raw).1.map (fun t => Address.toNat t.clock)
  simp only [List.map_map,Function.comp_def] at clocks
  exact clocks.nodup_iff.mpr (clock ▸ native_allocation_clock_unique w ok fit raw)

private theorem dispatch_valid_mem (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (mem : d ∈ physicalDispatches (observed w)) :
    d.Valid ∧ (d.flags.direct+d.flags.hook = 1 → d ∈ allocatingDispatches (observed w)) := by
  obtain ⟨r,kept,rfl⟩ := List.mem_map.mp mem
  obtain ⟨present,one⟩ := List.mem_filter.mp kept
  have enabled := of_decide_eq_true one
  have v := (native_dispatch_input_facts w ok fit raw r present).2 enabled
  refine ⟨v,fun gate => List.mem_map.mpr ⟨r,List.mem_filter.mpr ⟨present,?_⟩,rfl⟩⟩
  apply decide_eq_true
  simp only [ticketGate,enabled,gate,one_mul]

private theorem alloc_mem (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
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

/-- Every actual direct dispatcher has its own complete placement walk to the finish it
declared. Matching uses the full raw position multisets, route classification and unique
incoming allocation clock. Each group is an enabled, nonempty physical row. -/
theorem native_direct_placement (w : EnsembleWitness (native image source target)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ allocatingDispatches (observed w))
    (direct : d.flags.direct = 1) :
    ∃ groups : List (WriteEffects.Group F),
      Walk.IsWalk (fun g : WriteEffects.Group F => (g.previous,g.next)) (d.start d.flags) (d.finish d.flags) groups ∧
      ∀ g ∈ groups,g ∈ placementSteps (observed w) := by
  let seen := observed w
  let calls := physicalDispatches seen
  obtain ⟨paths,paired,ends,all⟩ := native_placement_walks w ok fit raw
  have appears : d ∈ (calls.zip paths).map Prod.fst := by rw [List.map_fst_zip paired.length_eq.le]; exact alloc_mem w ok fit raw d md
  obtain ⟨⟨actual,path⟩,both,e⟩ := List.mem_map.mp appears
  change actual = d at e
  subst actual
  have walk := (List.forall₂_iff_zip.mp paired).2 both
  have inPath := (List.of_mem_zip both).2
  have terminal := ends.mem_iff.mp (List.mem_map_of_mem (f := Prod.snd) inPath)
  obtain ⟨other,otherMem,endEq⟩ := List.mem_map.mp terminal
  have key := walk_key walk
  rw [← endEq] at key
  obtain ⟨ov,selected⟩ := dispatch_valid_mem w ok fit raw other otherMem
  have dv := ((native_allocation_tickets w ok fit raw).2 d md).1
  have bothRoutes : other.flags.sink = d.flags.sink := key.2.1
  have otherDirect := (direct_shape ov).1.mpr (bothRoutes.trans ((direct_shape dv).1.mp direct))
  have liveOther := selected (by rw [(direct_shape ov).2 otherDirect]; simp [DispatchFlags.hook])
  have sameTime : other.request.header.clock = d.request.header.clock := key.1
  have same := List.inj_on_of_nodup_map (native_dispatch_clocks w ok fit raw) liveOther md (congrArg Address.toNat sameTime)
  subst other
  exact ⟨path.1,endEq.symm ▸ walk,fun g m => all.mem_iff.mp (List.mem_flatMap.mpr ⟨path,inPath,m⟩)⟩

end SP1Clean.Export.WriteObservationAssembly
