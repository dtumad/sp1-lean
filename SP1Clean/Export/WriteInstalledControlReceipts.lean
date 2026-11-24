import SP1Clean.Export.InstalledHintRows
import SP1Clean.Export.CheckedLedger

/-! # HALT, ENTER and VERIFY on the public mixed witness

The decorated instruction at slot 58 keeps every ECALL cell. Its active messages, classified
by the full code read from those cells, fund the original receivers at slots 64 and 65.
The receiver ledgers retain the physical padding rows of the shared no-effect table.
-/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness Machine TraceGen FormalModel.Shard WriteSourceRegistry
open WriteMixedSourceTables

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {finish : HostHintQueue.State F}

attribute [local irreducible] base withSources preprocessing ofExecution

private theorem build_cells (w : EnsembleWitness (base image source target finish))
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)
    (i : Fin (base image source target finish).tables.length) :
    ((build w suffix reg).tables.map Table.table)[i.val]? = (w.tables.map Table.table)[i.val]? := by
  let layout := sameRows image source target finish
  let j : Fin (withSources image source target finish).tables.length := ⟨i.val,layout.length ▸ i.isLt⟩
  have inside : i.val < (installSources w).tables.length := (installSources w).same_length ▸ j.isLt
  have original : i.val < w.tables.length := w.same_length ▸ i.isLt
  have arrays : (build w suffix reg).tables.map Table.table = ((installSources w).tables ++ suffix).map Table.table := by
    dsimp only [build,Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables,withDerivedData_map_table]
  rw [arrays,List.getElem?_map,List.getElem?_append_left inside,List.getElem?_eq_getElem inside,
    List.getElem?_map,List.getElem?_eq_getElem original]
  exact congrArg some (layout.symm.rows w j)

/-- Full calls from active physical CPU rows whose released code selects the given receiver. -/
def controlMessages (cpu : Table F) (data : ProverData F) (k : ControlHandlers.Bucket) :=
  (HostCallLedger.calls cpu data).filter fun m => k.accepts (Word.toBitVec64 m.code)

private theorem selected_compiled (compiled : List MixedCompiledRow) (k : ControlHandlers.Bucket) :
    (((compiled.filterMap (MixedCompiledRow.syscallInput? (p := SP1Prime))).map HostCallChip.message).filter
      (fun m => k.accepts (Word.toBitVec64 m.code))) = compiled.filterMap (ControlHandlers.instructionMessage? k) := by
  induction compiled with
  | nil => rfl
  | cons r rs ih =>
    cases r with
    | ordinary => exact ih
    | syscall frontier base call =>
      simp only [List.filterMap_cons, MixedCompiledRow.syscallInput?, List.map_cons,
        List.filter_cons, ControlHandlers.instructionMessage?, syscallInstruction_eventMessage]
      rw [show Word.toBitVec64 (eventHostMessage (p := SP1Prime) call).code = call.rawCode from Target.toBitVec64_bitVecToWord _]
      cases k.accepts call.rawCode <;> simp [ih]

/-- The raw registered receiver position of each control handoff. -/
def controlPosition : ControlHandlers.Bucket → Nat
  | .halt => 64
  | .noop => 65

/-- The public witness's ECALL-to-control handoffs, selected from the actual instruction and
receiver cells. Each selected CPU push and each physical receiver site contributes to the count. -/
def ControlReceipts (full : EnsembleWitness (assembly image source target finish)) (events : List ExecutionEvent) : Prop :=
  ∃ cpu : Table F, full.tables[58]? = some cpu ∧
    cpu.interactionsWith HostCallChip.channel.toRaw = (cpu.table.map (Environment.fromArray · full.data)).map
      (fun e => HostCallChip.channel.pushedIfValue (HostCallLedger.input e).is_real (HostCallLedger.call e)) ∧
    ∀ k, ∃ receiver : Table F, full.tables[controlPosition k]? = some receiver ∧
      CheckedLedger (((controlMessages cpu full.data k).map HostCallChip.channel.pushedValue) ++
        receiver.interactionsWith HostCallChip.channel.toRaw) ((ControlHandlers.calls k events).length + receiver.length)

variable {events : List ExecutionEvent} (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image source target events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial source.realize events = some rows)
    (data : ProverData F) (hint : ProverHint F) (packets : List WriteObservations.Packet) (header : SP1PublicIO F)
    (remaining : WriteMixedControlTables.Remaining image source target finish)
    (suffix : List (Table F)) (reg : suffix.map Table.component = tables source target)

/-- The constructed control rows on the shared public witness fund exactly the physically
decoded HALT, ENTER and VERIFY sends of the same chronological CPU trace. -/
theorem installed_control_receipts :
    let fixed := WriteMixedControlTables.install run routed data remaining
    let host := WriteMixedFixedResources.install run routed data hint packets fixed
    let prior := WriteMixedHostTables.install run.1 data host
    let w := ofExecution run routed finish data hint header prior packets
    ControlReceipts (withPublicChecks (build w suffix reg)) events := by
  intro fixed host prior w
  let pre := build w suffix reg
  let full := withPublicChecks pre
  let id := WriteProbe.AccessInventory.Source.host .ecall
  let slot := originalSlot image source target finish id
  let i := slot.index
  let orig := MixedSyscallTable.table rows data hint (heights run routed).ecall
  have original : (w.tables.map Table.table)[i.val]? = some orig.table := by
    rw [List.getElem?_map,List.getElem?_eq_getElem (by rw [← w.same_length]; exact i.isLt)]
    apply congrArg some
    exact compiledSource_rows run routed data hint packets finish header prior id
  have joined := (build_cells w suffix reg i).trans original
  change (full.tables.map Table.table)[58]? = some orig.table at joined
  rw [List.getElem?_map] at joined
  obtain ⟨cpu, whereCPU, cells⟩ := Option.map_eq_some_iff.mp joined
  refine ⟨cpu,whereCPU,?_,?_⟩
  · have registered := publisher_at image source target finish id
    have inside : 58 < (withSources image source target finish).tables.length := (List.getElem?_eq_some_iff.mp registered).1
    have atFull : (preprocessing image source target finish).tables[58]? = some (publisher id) := by
      rw [(appended image source target finish).tables,List.getElem?_append_left inside]
      exact registered
    have actual := congrArg (fun cs : List (Component F) => cs[58]?) pre.tables_map_component
    change ((full.tables.map Table.component)[58]?) = _ at actual
    rw [List.getElem?_map,whereCPU,atFull,Option.map_some,Option.some.injEq] at actual
    have kept : cpu.interactionsWith HostCallChip.channel.toRaw = orig.interactionsWith HostCallChip.channel.toRaw := by
      apply Table.interactionsWith_eq_of_rows _ _ _ cells
      rw [actual]
      exact Receipt.many_interactions _ _ (fun _ _ => trivial) _ _ (by apply ne_of_apply_ne RawChannel.name; decide)
    rw [kept,HostCallLedger.table_values orig full.data rfl,cells]
  intro k
  let which := match k with | .halt => WriteMixedControlTables.Index.halt | .noop => .noop
  obtain ⟨actual, here, _, same, _, _, _, ledger⟩ :=
    WriteMixedControlTables.installed_at run routed data hint packets header remaining suffix reg which
  have pos : WriteMixedControlTables.position which = controlPosition k := by cases k <;> rfl
  refine ⟨actual, pos ▸ here, ?_⟩
  have active := MixedSyscallTable.active rows data full.data hint (heights run routed).ecall
  have sends : controlMessages cpu full.data k = rows.filterMap (ControlHandlers.instructionMessage? k) := by
    unfold controlMessages HostCallLedger.calls
    change (((HostCallLedger.activeRows cpu full.data).map (HostCallChip.message ∘ HostCallLedger.input)).filter _) = _
    rw [← List.map_map]
    have cpuRows : HostCallLedger.activeRows cpu full.data = HostCallLedger.activeRows orig full.data := by
      unfold HostCallLedger.activeRows
      rw [cells]
    rw [cpuRows,active]
    exact selected_compiled rows k
  obtain ⟨compiled,built,matched⟩ := ControlHandlers.host_matches run.1 data
  obtain rfl := Option.some.inj (routed.symm.trans built)
  have checks := matched k
  have height := congrArg List.length same
  change actual.length = (WriteMixedControlTables.table run routed data which).length at height
  rw [sends,ledger, height]
  cases k <;> exact ⟨(checks).1,(checks).2.1,(checks).2.2.1,(checks).2.2.2⟩

end SP1Clean.Export.WriteObservationAssembly
