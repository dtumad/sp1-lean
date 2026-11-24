import SP1Clean.Export.WriteMixedReadFunding

/-! # Original read-back publishers before canonical installation

The mixed instruction, host, refresh and boundary compilers generate the 31 physical Memory
sources directly. Their ordered signed ledger is independent of the other supervisor generators.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Semantics Soundness TraceGen Machine FormalModel.Shard
open WriteProbe WriteProbe.AccessInventory WriteProbe.SparseBoundary WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet)

/-- The 31 original read-back providers generated before assembling any other supervisor component. -/
noncomputable def compiledSource : Source → Table F
  | .finalizer ram =>
    let stream := MixedMemoryHistory.stream image source events rows
    let keys := WriteBoundaryBuild.demandKeys events packets
    finalTable ram (terminals source.sail.memorySnapshot stream keys data hint) data
      (terminals_fit ram _ _ _ (MixedMemoryHistory.canonical run.1 routed) data hint)
  | .refresh => table rows _ (heights run routed) data hint .refresh (by decide)
  | .host id => table rows _ (heights run routed) data hint (.host id) (by cases id with
      | ecall => decide
      | word last => cases last <;> decide)
  | .ordinary id => table rows _ (heights run routed) data hint (.ordinary id) (by change 6 ≤ 7 + _; omega)

/-- Exactly the two ordered finalizers precede the post-boundary Memory-source block. -/
theorem finalizer_or_later (id : Source) : (∃ ram, id = .finalizer ram) ∨ 6 ≤ position id := by
  cases id with
  | ordinary i => exact Or.inr (by change 6 ≤ 7 + _; omega)
  | host family => right; cases family with
    | ecall => decide
    | word last => cases last <;> decide
  | refresh => exact Or.inr (by decide)
  | finalizer ram => exact Or.inl ⟨ram,rfl⟩

/-- Every post-boundary entry of the source inventory uses its native bucket constructor. -/
theorem compiledSource_later (id : Source) (after : 6 ≤ position id) :
    compiledSource run routed data hint packets id = table rows _ (heights run routed) data hint id after := by
  cases id with
  | ordinary id => rfl
  | host family => rfl
  | refresh => rfl
  | finalizer ram => cases ram <;> contradiction

/-- Every original generated publisher has its registered native component. -/
theorem compiledSource_registered (id : Source) : (compiledSource run routed data hint packets id).component = original id := by
  rcases finalizer_or_later id with ⟨ram, rfl⟩ | after
  · rfl
  · rw [compiledSource_later run routed data hint packets id after]
    exact registered rows _ (heights run routed) data hint id after

/-- Each of the 31 physical publisher tables satisfies its constraints and channel guarantees. -/
theorem compiledSource_valid (id : Source) :
    let t := compiledSource run routed data hint packets id
    t.Constraints ∧ t.Guarantees := by
  rcases finalizer_or_later id with ⟨ram, rfl⟩ | after
  · exact (compiled_finalizers_valid _ _ _ (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram).2
  · rw [compiledSource_later run routed data hint packets id after]
    exact valid run routed data hint id after

variable (finish : HostHintQueue.State F) (header : SP1PublicIO F) (remaining : Remaining image source target finish)

/-- Canonicalizing the other supervisor slots leaves all compiled Memory-source arrays intact. -/
theorem compiledSource_rows (id : Source) :
    (raw (ofExecution run routed finish data hint header remaining packets) id).table =
      (compiledSource run routed data hint packets id).table := by
  let fit := heights run routed
  let history := HintReadTransfers.history image source events
  let stream := MixedMemoryHistory.stream image source events rows
  let keys := WriteBoundaryBuild.demandKeys events packets
  let canonical := MixedMemoryHistory.canonical run.1 routed
  let suffix := suffix image source target finish rows history fit data hint remaining
  have registered := suffix_registered image source target finish rows history fit data hint remaining
  rcases finalizer_or_later id with ⟨ram, rfl⟩ | after
  · exact WriteBoundaryBuild.finalizer_rows image source target finish stream keys canonical data hint header suffix registered ram
  · rw [compiledSource_later run routed data hint packets id after]
    exact raw_rows image source target finish rows history fit data hint remaining stream keys canonical header id after

/-- Canonical installation preserves the complete original ledger including order and all zero gates. -/
theorem compiled_records : records (raw (ofExecution run routed finish data hint header remaining packets)) =
    records (compiledSource run routed data hint packets) :=
  records_eq_of_arrays _ _ (compiledSource_rows run routed data hint packets finish header remaining)

end SP1Clean.Export.WriteMixedSourceTables
