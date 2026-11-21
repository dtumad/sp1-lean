import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.InstructionReleaseLinks
import SP1Clean.Soundness.InstructionMemoryEncoding
import SP1Clean.Soundness.LocalCoreEventUniqueness

/-! # Memory, clock, and jump-link encoding on the installed CPU walk

The physical State walk and the memory-grounded replay exhaust the same rows in strictly
increasing clock order. At each ordinary cut its physical row authenticates the decode, the
memory span and the jump link. Ordinary, HALT and syscall rows all enforce the active clock
phase through their physical CPUState reader.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Semantics NativeCore

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance releaseClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance releaseLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State (ZMod p)}

attribute [local irreducible] ensemble HostLocalCore.localWitness in
/-- The grounded replay and any exhaustive State walk have the same ordered event occurrences. -/
theorem PhysicalEventOrder.grounded (witness : EnsembleWitness (Installed image source target final))
    (valid : image.Valid) (checked : witness.Constraints) (funded : ExternallyBalanced witness)
    {events : List Machine.ExecutionEvent} (order : PhysicalEventOrder witness events) :
    ∃ carrier : HostHintReadCPU.GroundingCarrier (baseWitness witness), carrier.events = events := by
  let projected := baseWitness witness
  let host := HostHintQueueBoundary.projected projected
  let core := HostLocalCore.localWitness host
  have lowerChecked := baseWitness_constraints witness checked
  have lowerFunded := baseWitness_hostBalanced witness funded
  have coreChecked : core.Constraints := HostLocalCore.localWitness_constraints host
    (HostHintQueueBoundary.projected_constraints projected lowerChecked)
  have channels : LocalCore.OrderingChannels core := HostHintQueueBoundary.SourceWitness.orderingChannels projected lowerChecked lowerFunded
  obtain ⟨carrier⟩ := HostHintReadCPU.source_grounding_carrier valid projected lowerChecked lowerFunded
  change HostHintReadCPU.PhysicalEventOrder projected.data projected.publicInput (LocalCore.executionRows core) events at order
  obtain ⟨ordered, exhaust, walk, rfl⟩ := order
  have sorted (rows : List (ExecutionRow p)) (inventory : rows.Perm (LocalCore.executionRows core))
      (cpu : Walk.IsWalk (ExecutionRow.canonEdge projected.data) (initialBoundaryStateMessage projected.publicInput)
        (finalBoundaryStateMessage projected.publicInput) rows) :
      (rows.map fun row => StateMsg.timeNat (row.edge core.data).1).Pairwise (· < ·) := by
    apply LocalCore.ordered_times_pairwise core coreChecked channels inventory
    have edge : ExecutionRow.canonEdge core.data = ExecutionRow.canonEdge projected.data := funext fun row => row.canonEdge_setData _ _
    have header : core.publicInput = projected.publicInput :=
      (HostLocalCore.localWitness_publicInput host).trans (HostHintQueueBoundary.projected_publicInput projected)
    rwa [edge, header]
  have same : ordered = carrier.ordered := by
    apply (exhaust.trans carrier.exhaustive.symm).eq_of_pairwise (le := fun a b =>
      StateMsg.timeNat (a.edge core.data).1 < StateMsg.timeNat (b.edge core.data).1)
    · exact fun _ _ _ _ lt gt => (Nat.lt_asymm lt gt).elim
    · exact List.pairwise_map.mp (sorted ordered exhaust walk)
    · exact List.pairwise_map.mp (sorted carrier.ordered carrier.exhaustive carrier.cpuWalk)
  exact ⟨carrier, congrArg (List.map ExecutionRow.event) same.symm⟩

attribute [local irreducible] ensemble HostLocalCore.localWitness in
/-- The installed State walk supplies the full native encoding and released jump-link condition
at every replay cut. The same physical row authenticates the clock, decoder and memory span. -/
theorem PhysicalEventOrder.encoding (witness : EnsembleWitness (Installed image source target final))
    (valid : image.Valid) (checked : witness.Constraints) (funded : ExternallyBalanced witness)
    {events : List Machine.ExecutionEvent} (order : PhysicalEventOrder witness events) :
    ExecutionPath.Encoded ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) source.realize events ∧
    ExecutionPath.ReleaseLinks ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) source.realize events := by
  let projected := baseWitness witness
  let host := HostHintQueueBoundary.projected projected
  let core := HostLocalCore.localWitness host
  have lowerChecked := baseWitness_constraints witness checked
  have lowerFunded := baseWitness_hostBalanced witness funded
  have coreChecked : core.Constraints := HostLocalCore.localWitness_constraints host
    (HostHintQueueBoundary.projected_constraints projected lowerChecked)
  have channels := HostHintQueueBoundary.SourceWitness.orderingChannels projected lowerChecked lowerFunded
  obtain ⟨carrier, rfl⟩ := order.grounded witness valid checked funded
  have cut (n : ℕ) (current : ExecutionState) (event : Machine.ExecutionEvent)
      (atEvent : carrier.events[n]? = some event)
      (prefixReplay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize (carrier.events.take n) = some current) :
      eventEncodedAt (image.toGuestProgram valid) current event ∧
        (event = .ordinary → ReleaseLinkAt (image.toGuestProgram valid) current.sail) := by
    have covered := Nat.le_of_lt (List.getElem?_eq_some_iff.mp atEvent).1
    simp only [ExecutionCarrier.events, List.getElem?_map] at atEvent
    obtain ⟨row, atRow, rfl⟩ := Option.map_eq_some_iff.mp atEvent
    have active := carrier.exhaustive.mem_iff.mp (List.mem_of_getElem? atRow)
    have phase := (LocalCore.executionRows_clock_of_orderingChannels core coreChecked channels active).2.2
    rw [row.edge_setData core.data projected.data, ExecutionRow.edge_eq_facts] at phase
    have time := carrier.time_of_ordered_at atRow
    rw [(HostHintReadCPU.eventFacts_state_fetch _ _ _).1, carrier.timeline_events lowerChecked lowerFunded,
      eventTimeline_start_le _ _ _ covered] at time
    have currentClock : current.clock = StateMsg.timeNat (row.facts projected.data).statePull :=
      (replayEvents?_clock prefixReplay).trans time.symm
    rw [← currentClock] at phase
    cases row with
    | instruction row =>
      obtain ⟨_, _, _, _, fixed, dynamic, real, decoded, atPc, configured⟩ :=
        carrier.instruction_step_at valid lowerChecked lowerFunded atRow prefixReplay
      exact ⟨⟨phase, fun _ => row.ordinaryEncodedAt fixed dynamic real decoded atPc⟩,
        fun _ => row.releaseLinkAt fixed dynamic real decoded atPc configured⟩
    | halt row => exact ⟨⟨phase, by rintro ⟨⟩⟩, by rintro ⟨⟩⟩
    | syscall row => exact ⟨⟨phase, by rintro ⟨⟩⟩, by rintro ⟨⟩⟩
  exact ⟨fun n current event label replay => (cut n current event label replay).1,
    fun n current label replay => (cut n current .ordinary label replay).2 rfl⟩

end SP1Clean.Soundness.HostFinalMemory
