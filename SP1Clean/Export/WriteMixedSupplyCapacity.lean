import SP1Clean.Export.WriteMixedReadFunding
import SP1Clean.Proofs.Completeness.WriteCountedCost

/-! # Supply indices and source validity for the generated WRITE observer

The actual padded original tables fit the counted supplier's array type. Its row count is
computed from the physical occurrences. The native address space, execution duration and
HINT byte charge suffice even before constructing the remaining supervisor components.
-/

namespace SP1Clean.Export.WriteMixedSourceTables

open Circuit Air.Flat Channels Semantics Soundness TraceGen Machine FormalModel.Shard WitnessGeneration
open WriteProbe WriteProbe.AccessInventory WriteProbe.SparseBoundary WriteSourceRegistry

private abbrev F := ZMod SP1Prime

private theorem finalizer_or_later (id : Source) : (∃ ram, id = .finalizer ram) ∨ 6 ≤ position id := by
  cases id with
  | ordinary i => exact Or.inr (by change 6 ≤ 7 + _; omega)
  | host family => right; cases family with
    | ecall => decide
    | word last => cases last <;> decide
  | refresh => exact Or.inr (by decide)
  | finalizer ram => exact Or.inl ⟨ram,rfl⟩

private theorem constraints_of_rows {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}
    (w : EnsembleWitness (base image source target finish)) (id : Source) (t : Table F) (registered : t.component = original id)
    (same : (raw w id).table = t.table) (checked : t.Constraints) : (raw w id).Constraints := by
  have originalMem := List.mem_of_getElem? (original_at image source target finish id)
  have free := HostObserved.lookupFree (image := image) (source := source) (target := target) (final := finish) (original id) originalMem
  intro row occurs
  have valid := checked row (same ▸ occurs)
  rw [← registered] at free
  have physical := t.component.constraintsHold_setData (data' := (raw w id).data) free valid
  change (raw w id).component.operations.ConstraintsHold (Environment.fromArray row (raw w id).data)
  rwa [raw_registered, ← registered]

variable {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (ResourceLimits.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F)
    (header : SP1PublicIO F) (remaining : Remaining image source target finish)
    (packets : List WriteObservations.Packet)

/-- All original physical Memory sources obey their constraints after canonical data derivation,
independently of which tables the other generators install in their own slots. -/
theorem source_checked (id : Source) : (raw (ofExecution run routed finish data hint header remaining packets) id).Constraints := by
  let s := suffix image source target finish rows _ (heights run routed) data hint remaining
  have reg := suffix_registered image source target finish rows _ (heights run routed) data hint remaining
  rcases finalizer_or_later id with ⟨ram, rfl⟩ | outside
  · exact constraints_of_rows _ _ _ rfl
      (WriteBoundaryBuild.finalizer_rows image source target finish _ _ (MixedMemoryHistory.canonical run.1 routed)
        data hint header s reg ram)
      (compiled_finalizers_valid _ _ _ (MixedMemoryHistory.addresses_in_layout run.1 routed) data hint ram).2.1
  · exact constraints_of_rows _ _ _ (registered ..)
      (raw_rows image source target finish rows _ (heights run routed) data hint remaining _ _ _ header id outside)
      (valid run routed data hint id outside).1

private theorem later_height (id : Source) (outside : 6 ≤ position id) :
    (table rows (HintReadTransfers.history image source events) (heights run routed) data hint id outside).length ≤ 2 ^ 50 := by
  obtain ⟨actual, generated, size⟩ := admissibleExecution_routeMixedRows run.1
  have length : rows.length = events.length := Option.some.inj (routed.symm.trans generated) ▸ size
  have count := event_count_le_ticks events
  have ticks := run.1.1.clock
  have last : target.clock < 2 ^ 48 := run.1.2.2.2.2.2.1
  have size : rows.length < 2 ^ 48 := by omega
  cases id with
  | ordinary id =>
    rw [table, InstalledInstructionTables.table_length]
    apply demandHeight_le_pow
    have len := (EventBuckets.length_le (rows.filterMap MixedCompiledRow.ordinaryObservation?) id).trans (List.length_filterMap_le ..)
    change (EventBuckets.ofChronological _ _).length ≤ _
    omega
  | host family => cases family with
    | ecall =>
      rw [table, MixedSyscallTable.table_length]
      apply demandHeight_le_pow
      have count := List.length_filterMap_le (MixedCompiledRow.syscallInput? (p := SP1Prime)) rows
      omega
    | word last =>
      rw [table, HintReadTransfers.wordTable_length]
      exact demandHeight_le_pow ((HintReadTransfers.selected_count_bound run.1 last).trans (by decide))
  | refresh =>
    obtain ⟨inputs, bumped, _, mem, _, _, _⟩ := admissibleExecution_mixedBumpInventory run.1
    rw [routeBumpInputs?, routed, Option.map_some] at bumped
    obtain rfl := Option.some.inj bumped
    rw [table, InstalledAssembly.bumpTables_registerLength]
    apply demandHeight_le_pow
    omega
  | finalizer ram => cases ram <;> contradiction

/-- The released execution's actual generated source heights admit all 31 source sites in one
64-bit Lean array. The field-capacity condition for future verifier acceptance remains separate. -/
theorem supply_index_fit (requests : List (Counted.Request (Counted.live (records (raw
    (ofExecution run routed finish data hint header remaining packets)))).length F)) :
    let w := ofExecution run routed finish data hint header remaining packets
    demandHeight (Counted.allocated (Counted.live (records (raw w))) requests).length ≤ UInt64.size := by
  let w := ofExecution run routed finish data hint header remaining packets
  have height (id : Source) : (raw w id).length ≤ 2 ^ 50 := by
    rcases finalizer_or_later id with ⟨ram, rfl⟩ | outside
    · change (raw w (.finalizer ram)).table.length ≤ _
      have located := WriteBoundaryBuild.finalizer_rows image source target finish _ (WriteBoundaryBuild.demandKeys events packets) (MixedMemoryHistory.canonical run.1 routed)
        data hint header _ (suffix_registered image source target finish rows _ (heights run routed) data hint remaining) ram
      change (raw w (.finalizer ram)).table = _ at located
      rw [located, finalTable_length]
      exact (demandHeight_le_pow (terminal_count_bound ram _ _ _ (MixedMemoryHistory.canonical run.1 routed) data hint)).trans (by decide)
    · change (raw w id).table.length ≤ _
      rw [show (raw w id).table = _ from raw_rows image source target finish rows _ (heights run routed) data hint remaining _ _ _ header id outside]
      exact later_height run routed data hint id outside
  have width (id : Source) : perRow (p := SP1Prime) id ≤ 3 := by
    cases id with
    | ordinary id => exact (OrdinarySources.accessCount_bounds id).2
    | host family => cases family <;> simp only [perRow] <;> decide
    | refresh => decide
    | finalizer _ => change 1 ≤ 3; decide
  have count : (records (raw w)).length ≤ 31 * (2 ^ 50 * 3) := by
    rw [records_length _ (raw_registered w)]
    calc
      _ ≤ (sources.map (fun _ => 2 ^ 50 * 3)).sum := List.sum_le_sum (fun id _ => Nat.mul_le_mul (height id) (width id))
      _ = _ := by rw [List.map_const', List.sum_replicate, smul_eq_mul, sources_length]
  have active : (Counted.live (records (raw w))).length ≤ (records (raw w)).length := by
    simp only [Counted.live, List.length_map]
    exact List.length_filter_le ..
  change demandHeight (Counted.allocated (Counted.live (records (raw w))) requests).length ≤ UInt64.size
  apply demandHeight_le_pow (exponent := 64)
  simp only [Counted.allocated, List.length_ofFn]
  omega

end SP1Clean.Export.WriteMixedSourceTables
