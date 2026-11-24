import SP1Clean.Export.WriteMixedSupplyCapacity
import SP1Clean.Export.WriteMixedSourceRecords
import SP1Clean.Export.WriteGeneratedEcallBounds
import SP1Clean.Export.WriteGeneratedOrdinaryBounds
import SP1Clean.Export.WriteGeneratedHostReadbacks

/-! # All original mixed read-back source clocks

A positive source occurrence selects its own registered table and physical row. Generated
ordinary, ECALL, HINT_READ, refresh and finalizer timestamps all fit the four 24-bit limbs
used by the counted read-back supplier.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Semantics Soundness TraceGen Machine FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory WriteProbe.SparseBoundary WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F)
    (packets : List WriteObservations.Packet)

/-- Every generated unit receipt has bounded clocks, including original sources whose contents
no WRITE request used. -/
theorem compiled_bounded : ∀ r ∈ Counted.live (records (compiledSource run routed data hint packets)), Counted.Bounded r := by
  let sources := compiledSource run routed data hint packets
  let fit := heights run routed
  let stream := MixedMemoryHistory.stream image source events rows
  let canonical := MixedMemoryHistory.canonical run.1 routed
  change ∀ r ∈ Counted.live (records sources), Counted.Bounded r
  intro r member
  obtain ⟨⟨weight,r⟩, paid, rfl⟩ := List.mem_map.mp member
  obtain ⟨actual, unit⟩ := List.mem_filter.mp paid
  have gate : weight = 1 := of_decide_eq_true unit
  subst weight
  obtain ⟨id, _, found⟩ := List.mem_flatMap.mp actual
  obtain ⟨cells, occurs, receipt⟩ := List.mem_flatMap.mp found
  change cells ∈ (sources id).table at occurs
  change (1, r) ∈ rowRecords id (Environment.fromArray cells (sources id).data) at receipt
  cases id with
  | ordinary id =>
    exact generated_ordinary_bounded run routed id data _ hint (fit.ordinary id) occurs receipt
  | host family => cases family with
    | ecall =>
      exact generated_ecall_bounded run.1 routed data _ hint fit.ecall occurs receipt
    | word last =>
      exact generated_hint_bounded run.1 last data _ (fit.hint last) occurs receipt
  | refresh =>
    obtain ⟨inputs, bumped, _, _, _, valid, _⟩ := admissibleExecution_mixedBumpInventory run.1
    rw [routeBumpInputs?, routed, Option.map_some] at bumped
    obtain rfl := Option.some.inj bumped
    exact generated_refresh_bounded _ _ valid data _ fit.memory fit.state occurs receipt
  | finalizer ram =>
    exact finalTable_bounded ram _ (terminals_ordered _ _ _ canonical data hint)
      (fun _ mem => terminal_bounded _ _ _ (fun _ used => MixedMemoryHistory.posted_clock_bound run.1 routed used) data hint mem)
      data _ (terminals_fit ram _ stream _ canonical data hint) occurs receipt

/-- The original source receipts remain bounded on every canonical supervisor built around this execution. -/
theorem source_bounded (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F)
    (header : SP1PublicIO F) (remaining : Remaining image source target finish) (packets : List WriteObservations.Packet) :
    let w := ofExecution run routed finish data hint header remaining packets
    ∀ r ∈ Counted.live (records (raw w)), Counted.Bounded r := by
  dsimp only
  rw [compiled_records run routed data hint packets finish header remaining]
  exact compiled_bounded run routed data hint packets

end SP1Clean.Export.WriteMixedSourceTables
