import SP1Clean.Export.InstalledBumpTables
import SP1Clean.Proofs.Chips.WriteProbeRefresh
import SP1Clean.Soundness.WriteReadbackSupply
import SP1Clean.Soundness.SystemMemoryRows
import SP1Clean.Proofs.Completeness.MemoryReadbackIntervals

/-! # Constructing physical WRITE sources from actual mixed-execution register refreshes

The same mixed route produces both the original register timestamps and the additional sources.
Private query counts can be chosen freely. Neither validity nor the physical row bounds depend on
their choice. The source and its fan-out use the same ordered read-back data and disabled padding.
-/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Semantics Machine TraceGen FormalModel.Shard WriteProbe
open WriteProbe.ReadbackSupply

/-- The precise read-back packet emitted by the original row for one semantic register refresh. -/
def refreshEventReceipt (event : MemoryBumpEvent) : Readback Fp := refreshReadback (memoryBumpCols event)

private theorem pack (x d : ℕ) : ((x % d : ℕ) : Fp) + ((x / d : ℕ) : Fp) * (d : Fp) = (x : Fp) := by
  simpa only [Nat.cast_add, Nat.cast_mul] using congrArg (fun n : ℕ => (n : Fp)) (Nat.mod_add_div' x d)

private theorem refreshEventReceipt_eq (e : MemoryBumpEvent) :
    refreshEventReceipt e = ⟨#v[(e.addr : Fp), 0, 0], (e.prevTs / 2 ^ 24 : ℕ), (e.prevTs % 2 ^ 24 : ℕ),
      (e.currTs / 2 ^ 24 : ℕ), (e.currTs % 2 ^ 24 : ℕ), wordOfNat e.value⟩ := by
  have high := pack (e.currTs / 2 ^ 24) 256
  have low := pack (e.currTs % 2 ^ 24) 65536
  simp only [Nat.cast_ofNat] at high low
  simp only [refreshEventReceipt, refreshReadback, memoryBumpCols, memoryAccessCols_prev_high,
    memoryAccessCols_prev_low, memoryAccessCols_prev_value, Nat.shiftRight_eq_div_pow]
  exact congrArg₂ (fun a b => Readback.mk _ _ _ a b _) high low

/-- The actual generated refresh retains every canonical predecessor and post field on
the original Memory bus. The 64-bit word representation also agrees for arbitrary natural inputs. -/
theorem refresh_transfers (e : MemoryBumpEvent) (valid : e.WellFormed) :
    let event := MemoryHistoryAccess.ofMemoryBump e
    Soundness.MemoryBumpChip.pulledMessage (memoryBumpCols (p := SP1Prime) e) = event.pulledEntry.toMemoryMsg ∧
      Soundness.MemoryBumpChip.pushedMessage (memoryBumpCols (p := SP1Prime) e) = event.pushedEntry.toMemoryMsg := by
  obtain ⟨addr, _, _⟩ := valid
  have low : e.addr % 2 ^ 16 = e.addr := by omega
  have mid : e.addr / 2 ^ 16 % 2 ^ 16 = 0 := by omega
  have high : e.addr / 2 ^ 32 % 2 ^ 16 = 0 := by omega
  have small : e.addr % 2 ^ 5 = e.addr := by omega
  have value : wordOfNat (p := SP1Prime) (BitVec.ofNat 64 e.value).toNat = wordOfNat e.value := by
    apply Word.eq_of_toBitVec64_eq (wordOfNat_isU64 _) (wordOfNat_isU64 _)
    rw [toBitVec64_wordOfNat, toBitVec64_wordOfNat, BitVec.ofNat_toNat]
    rfl
  change wordOfNat (p := SP1Prime) (e.value % 2 ^ 64) = wordOfNat e.value at value
  have upper := pack (e.currTs / 2 ^ 24) 256
  have lower := pack (e.currTs % 2 ^ 24) 65536
  simp only [Nat.cast_ofNat] at upper lower
  dsimp only
  simp only [MemoryHistoryAccess.ofMemoryBump, MemoryHistoryAccess.pulledEntry, MemoryHistoryAccess.pushedEntry,
    MemRecordEntry.toMemoryMsg, MemLoc.busAddress, value, BitVec.toNat_ofNat, small, low, mid, high, Nat.cast_zero,
    Soundness.MemoryBumpChip.pulledMessage, Soundness.MemoryBumpChip.pushedMessage, memoryBumpCols,
    memoryAccessCols_prev_value, memoryAccessCols_prev_high, memoryAccessCols_prev_low, Nat.shiftRight_eq_div_pow,
    true_and]
  exact congrArg₂ (fun a b => Channels.MemoryMsg.mk a b (e.addr : Fp) 0 0 (wordOfNat e.value)) upper lower

private theorem validInput (e : MemoryBumpEvent) (honest : e.WellFormed) (weight : Fp) :
    Valid (populate (refreshEventReceipt e) weight) ∧ (populate (refreshEventReceipt e) weight).receipt = refreshEventReceipt e := by
  have primeBound := Fact.out (p := 2 ^ 24 < SP1Prime)
  have advance := honest.increases
  have fits := honest.currLt
  rw [refreshEventReceipt_eq]
  apply populate_valid <;> rw [ZMod.val_natCast_of_lt (by omega)] <;> omega

private theorem trueClock (time : ℕ) (fits : time < 2 ^ 48) :
    clkNat ((time / 2 ^ 24 : ℕ) : Fp) ((time % 2 ^ 24 : ℕ) : Fp) = time := by
  have field := Fact.out (p := 2 ^ 24 < SP1Prime)
  unfold clkNat
  repeat' rw [ZMod.val_natCast_of_lt (by omega)]
  omega

/-- At every time admitted by a constructed refresh version, including both endpoints,
the physical value is exactly the held word in its original chronological location history. -/
theorem refreshVersion_heldAt (e : MemoryBumpEvent) (honest : e.WellFormed) (count : Fp)
    (history : MemoryLocationHistory) (chain : history.IsRecordChain)
    (strict : ∀ a ∈ history.accesses, a.previous < a.current)
    (member : MemoryHistoryAccess.ofMemoryBump e ∈ history.accesses) {time : ℕ}
    (covers : let version := (populate (refreshEventReceipt e) count).version
              Address.toNat version.lower ≤ time ∧ time ≤ Address.toNat version.upper) :
    MemoryHistoryAccess.heldAt history.first.pulled time history.accesses =
      Word.toBitVec64 (populate (refreshEventReceipt e) count).version.value := by
  obtain ⟨valid, receipt⟩ := validInput e honest count
  have lower := (populate (refreshEventReceipt e) count).previous.time valid.2.2.1
  have upper := (populate (refreshEventReceipt e) count).current.time valid.2.2.2
  let r := populate (refreshEventReceipt e) count
  change Address.toNat r.version.lower = clkNat r.receipt.previousHigh r.receipt.previousLow at lower
  change Address.toNat r.version.upper = clkNat r.receipt.currentHigh r.receipt.currentLow at upper
  change r.receipt = refreshEventReceipt e at receipt
  rw [receipt, refreshEventReceipt_eq, trueClock _ (honest.increases.trans honest.currLt)] at lower
  rw [receipt, refreshEventReceipt_eq, trueClock _ honest.currLt] at upper
  change Address.toNat r.version.lower ≤ time ∧ time ≤ Address.toNat r.version.upper at covers
  rw [lower, upper] at covers
  rw [history.heldAt_memoryBump chain strict member covers]
  change BitVec.ofNat 64 e.value = Word.toBitVec64 (refreshEventReceipt e).value
  rw [refreshEventReceipt_eq]
  exact (toBitVec64_wordOfNat e.value).symm

/-- Gate, output count and both private messages on a disabled supply row. -/
def refreshSupplyPadding : ReadbackSupply.Inputs Fp := ⟨#v[0, 0, 0], ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, #v[0, 0, 0, 0], 0, 0⟩

private theorem disabled_valid : Valid refreshSupplyPadding := by simp [Valid, refreshSupplyPadding, ClockParts.Bounded]

/-- The explicit disabled physical input is exactly the installed demand scheduler's padding. -/
theorem refreshSupply_generation_padding :
    ∃ mode, (component (p := SP1Prime)).generation = .demand mode ∧ mode.padding = refreshSupplyPadding := by
  refine ⟨_, rfl, ?_⟩
  apply ProvableType.toElements_inj_iff.mp
  decide +kernel

/-- All chronological live supply rows followed by the released demand-padding suffix. -/
def refreshSupplyInputs (events : List MemoryBumpEvent) (counts : Readback Fp → Fp) : List (ReadbackSupply.Inputs Fp) :=
  (events.map fun event => populate (refreshEventReceipt event) (counts (refreshEventReceipt event))) ++
    List.replicate (WitnessGeneration.demandPadding events.length) refreshSupplyPadding

private theorem supply_height (events : List MemoryBumpEvent) (counts : Readback Fp → Fp) :
    (refreshSupplyInputs events counts).length = WitnessGeneration.demandHeight events.length := by
  simp only [refreshSupplyInputs, List.length_append, List.length_map, List.length_replicate,
    WitnessGeneration.add_demandPadding]

private theorem inputs_valid (events : List MemoryBumpEvent) (counts : Readback Fp → Fp)
    (wf : ∀ event ∈ events, event.WellFormed) : ∀ input ∈ refreshSupplyInputs events counts, Valid input := by
  intro input member
  rcases List.mem_append.mp member with live | pad
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp live
    exact (validInput e (wf e he) _).1
  · exact (List.eq_of_mem_replicate pad) ▸ disabled_valid

/-- An honest source table for exactly these mixed-path refreshes, with all witnesses generated by Clean. -/
def refreshSupplyTable (events : List MemoryBumpEvent) (counts : Readback Fp → Fp) (data : ProverData Fp)
    (bound : WitnessGeneration.demandHeight events.length ≤ UInt64.size) : Table Fp :=
  let rows := refreshSupplyInputs events counts
  Table.build component rows (component.inputData rows data) (ProverHint.empty _)
    ((supply_height events counts).trans_le bound) (by trivial) (component.inputData_consistent rows data)

/-- Every private pull, including padding, corresponds to the supplied complete genuine refresh record. -/
theorem refreshSupply_receipts (events : List MemoryBumpEvent) (counts : Readback Fp → Fp) (data : ProverData Fp)
    (bound : WitnessGeneration.demandHeight events.length ≤ UInt64.size) :
    (refreshSupplyTable events counts data bound).interactionsWith readbackChannel.toRaw =
      (refreshSupplyInputs events counts).map fun input => readbackChannel.pulledIfValue input.active input.receipt := by
  unfold refreshSupplyTable
  refine (Table.build_interactions component (refreshSupplyInputs events counts) _ _ _ _ _ readbackChannel.toRaw).trans ?_
  simp only [receipt_values, Component.rowInput_buildRow]
  exact List.map_eq_flatMap.symm

private abbrev memory := Soundness.providerTableFor (p := SP1Prime) .memoryBump

private def physicalInputs (events : List MemoryBumpEvent) : List (MemoryBumpChip.Inputs Fp) :=
  memoryBumpTraceInputs events ++ List.replicate (WitnessGeneration.demandPadding events.length) MemoryBumpChip.paddingInputs

/-- Both signed original Memory ledgers of the generated table are the complete ordered
lists of actual refreshes. Disabled rows contribute zero on both sides. -/
theorem bumpTables_registerMemory (regs : List MemoryBumpEvent) (states : List StateBumpEvent) (data : ProverData Fp)
    (mh : WitnessGeneration.demandHeight regs.length ≤ UInt64.size)
    (sh : WitnessGeneration.demandHeight states.length ≤ UInt64.size) (valid : ∀ e ∈ regs, e.WellFormed) :
    let t := (bumpTables regs states data mh sh).1
    let ledger := Soundness.typedTableInteractionsWith t Channels.memoryChannel
    Soundness.consumedMessages ledger = regs.map (fun e => (MemoryHistoryAccess.ofMemoryBump e).pulledEntry.toMemoryMsg) ∧
      Soundness.producedMessages ledger = regs.map (fun e => (MemoryHistoryAccess.ofMemoryBump e).pushedEntry.toMemoryMsg) := by
  intro t ledger
  have sides := Soundness.memoryBumpRows_projection t t.data rfl (bumpTables_registerValid _ _ _ _ _ valid).1
  have decoded : Soundness.activeSystemRows t (Soundness.memoryBumpRow t.data) (·.is_real) = regs.map memoryBumpCols := by
    have roundtrip (row : MemoryBumpChip.Inputs Fp) :
        Soundness.memoryBumpRow t.data (memory.buildRow row t.data (ProverHint.empty _)) = row :=
      memory.rowInput_buildRow row t.data t.data (ProverHint.empty _)
    let build := fun (r : MemoryBumpChip.Inputs Fp) => memory.buildRow r t.data (ProverHint.empty _)
    have recover : (t.table.map (Soundness.memoryBumpRow t.data)) = physicalInputs regs := by
      rw [bumpTables_registerRows]
      exact (List.map_map (l := physicalInputs regs) (f := build) (g := Soundness.memoryBumpRow t.data)).trans
        (by simp [Function.comp_def, build, roundtrip])
    rw [Soundness.activeSystemRows, recover]
    simp [physicalInputs, memoryBumpTraceInputs, List.filter_append, List.filter_map, Function.comp_def,
      show ∀ e : MemoryBumpEvent, (memoryBumpCols (p := SP1Prime) e).is_real = 1 from fun _ => rfl,
      show (MemoryBumpChip.paddingInputs (p := SP1Prime)).is_real = 0 from rfl]
  dsimp only [ledger]
  rw [sides.1, sides.2, decoded]
  simp only [List.flatMap_map, Soundness.MemoryBumpChip.memoryPairs, List.map_cons, List.map_nil, ← List.map_eq_flatMap]
  exact ⟨List.map_congr_left (fun e member => (refresh_transfers e (valid e member)).1),
    List.map_congr_left (fun e member => (refresh_transfers e (valid e member)).2)⟩

private theorem original_receipts (regs : List MemoryBumpEvent) (states : List StateBumpEvent) (data : ProverData Fp)
    (mh : WitnessGeneration.demandHeight regs.length ≤ UInt64.size)
    (sh : WitnessGeneration.demandHeight states.length ≤ UInt64.size) :
    (publishRefresh (bumpTables regs states data mh sh).1 (by rfl)).interactionsWith readbackChannel.toRaw =
      (physicalInputs regs).map fun r => readbackChannel.pushedIfValue r.is_real (refreshReadback r) := by
  refine (publishRefresh_receipts (bumpTables regs states data mh sh).1 (by rfl)).trans ?_
  let original := (bumpTables regs states data mh sh).1
  rw [bumpTables_registerRows regs states data mh sh]
  let build (r : MemoryBumpChip.Inputs Fp) : Array Fp := memory.buildRow r original.data (ProverHint.empty _)
  let observe (row : Array Fp) : Interaction Fp :=
    let input := valueFromOffset MemoryBumpChip.Inputs 0 (original.environment row)
    readbackChannel.pushedIfValue input.is_real (refreshReadback input)
  refine (List.map_map (f := build) (g := observe) (l := physicalInputs regs)).trans ?_
  apply List.map_congr_left
  intro r _
  have recovered := memory.rowInput_buildRow r original.data original.data (ProverHint.empty _)
  change valueFromOffset MemoryBumpChip.Inputs 0 _ = r at recovered
  exact congrArg (fun r : MemoryBumpChip.Inputs Fp => readbackChannel.pushedIfValue r.is_real (refreshReadback r)) recovered

private theorem balance_append (a b : List (Interaction Fp)) (msg : Array Fp) :
    balanceOf (a ++ b) msg = balanceOf a msg + balanceOf b msg := by
  simp [balanceOf]

private theorem opposite (rows : List (Fp × Readback Fp)) :
    LogUpBalanced (rows.map (fun r => readbackChannel.pushedIfValue r.1 r.2) ++
      rows.map (fun r => readbackChannel.pulledIfValue r.1 r.2)) := by
  intro msg
  rw [balance_append]
  induction rows with
  | nil => simp [balanceOf]
  | cons row rest ih =>
    simp only [List.map_cons, balanceOf_cons, Interaction.signedMult, Channel.pushedIfValue, Channel.pulledIfValue]
    simp only [Channel.pushedIfValue, Channel.pulledIfValue] at ih
    split <;> linear_combination ih

/-- On this exact private ledger each live row has the opposite signed partner, and both
padded tables retain all disabled occurrences. This proves the raw field tally for every
payload without assuming a count bound or any property of the query multiplicities. -/
theorem refreshSupply_balanced (regs : List MemoryBumpEvent) (states : List StateBumpEvent) (sourceData supplyData : ProverData Fp)
    (counts : Readback Fp → Fp) (valid : ∀ e ∈ regs, e.WellFormed)
    (mh : WitnessGeneration.demandHeight regs.length ≤ UInt64.size)
    (sh : WitnessGeneration.demandHeight states.length ≤ UInt64.size) :
    LogUpBalanced ((publishRefresh (bumpTables regs states sourceData mh sh).1 (by rfl)).interactionsWith readbackChannel.toRaw ++
      (refreshSupplyTable regs counts supplyData mh).interactionsWith readbackChannel.toRaw) := by
  rw [original_receipts, refreshSupply_receipts]
  let rows := (physicalInputs regs).map fun r => (r.is_real, refreshReadback r)
  have matchRows : (refreshSupplyInputs regs counts).map (fun r => (r.active, r.receipt)) = rows := by
    simp only [refreshSupplyInputs, rows, physicalInputs, memoryBumpTraceInputs, List.map_append, List.map_map,
      List.map_replicate, Function.comp_def]
    apply congrArg₂ List.append
    · apply List.map_congr_left
      intro e mem
      exact Prod.ext rfl (validInput e (valid e mem) _).2
    · rfl
  have source : (physicalInputs regs).map (fun r => readbackChannel.pushedIfValue r.is_real (refreshReadback r)) =
      rows.map (fun r => readbackChannel.pushedIfValue r.1 r.2) := by simp [rows, List.map_map]
  have pulls := congrArg (fun inputs : List (Fp × Readback Fp) => inputs.map fun r => readbackChannel.pulledIfValue r.1 r.2) matchRows
  simp only [List.map_map, Function.comp_def] at pulls
  rw [source, pulls]
  exact opposite rows

/-- Reserve the generated supply input entry before building both original bump tables. -/
def seedRefreshData (regs : List MemoryBumpEvent) (counts : Readback Fp → Fp) (data : ProverData Fp) :=
  component.inputData (refreshSupplyInputs regs counts) data

private theorem shared_data (regs : List MemoryBumpEvent) (states : List StateBumpEvent)
    (counts : Readback Fp → Fp) (data : ProverData Fp)
    (mh : WitnessGeneration.demandHeight regs.length ≤ UInt64.size)
    (sh : WitnessGeneration.demandHeight states.length ≤ UInt64.size) :
    let base := (bumpTables regs states (seedRefreshData regs counts data) mh sh).1
    (refreshSupplyTable regs counts base.data mh).data = base.data := by
  let base := (bumpTables regs states (seedRefreshData regs counts data) mh sh).1
  change ProverData.mk _ base.data.publicInput = ProverData.mk _ base.data.publicInput
  apply congrArg (fun tables => ProverData.mk tables base.data.publicInput)
  funext name arity
  by_cases same : name = (component (p := SP1Prime)).circuit.name
  · subst name
    rfl
  · simp only [Component.inputData, same, ↓reduceIte]
    rfl

/-- Actual mixed execution constructs the registered refresh table bearing its original channels,
and a checked, independently padded version source of the same height. Every active record is
an actual routed refresh with the exact two clocks and unchanged word. -/
theorem admissibleExecution_writeRefresh (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (counts : Readback Fp → Fp) (data : ProverData Fp) :
    ∃ inputs, routeBumpInputs? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial
      ctx.source.realize events = some inputs ∧
      ∃ mh sh, let regs := MixedBumpInput.memoryRows inputs
               let state := MixedBumpInput.stateRows inputs
               let base := (bumpTables regs state (seedRefreshData regs counts data) mh sh).1
               let marked := publishRefresh base (by rfl)
               let supply := refreshSupplyTable regs counts base.data mh
               marked.table = base.table ∧ supply.data = marked.data ∧ marked.data.publicInput = data.publicInput ∧ marked.Constraints ∧ supply.Constraints ∧
               LogUpBalanced (marked.interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw) ∧
               marked.length = WitnessGeneration.demandHeight regs.length ∧ supply.length = marked.length ∧
               ∀ event ∈ regs, Valid (populate (refreshEventReceipt event) (counts (refreshEventReceipt event))) ∧
                 (populate (refreshEventReceipt event) (counts (refreshEventReceipt event))).receipt = refreshEventReceipt event := by
  obtain ⟨inputs, route, _, _, _, valid, _⟩ := admissibleExecution_mixedBumpInventory execution
  let regs := MixedBumpInput.memoryRows inputs
  let state := MixedBumpInput.stateRows inputs
  let seeded := seedRefreshData regs counts data
  obtain ⟨other, same, mh, sh, _, _, _, publicData, height, _, checked, _⟩ := bump_constructed_tables ctx execution seeded
  have equal : other = inputs := Option.some.inj (same.symm.trans route)
  subst other
  refine ⟨inputs, route, mh, sh, rfl, shared_data regs state counts data mh sh, publicData,
    (publishRefresh_constraints _ _).mpr checked, ?_, refreshSupply_balanced _ _ _ _ _ valid _ _, height, ?_, ?_⟩
  · let rows := refreshSupplyInputs regs counts
    let canonical := (bumpTables regs state seeded mh sh).1.data
    exact Table.build_constraints component rows (component.inputData rows canonical) (ProverHint.empty _)
      ((supply_height regs counts).trans_le mh) (by trivial) (component.inputData_consistent rows canonical)
      (inputs_valid regs counts valid)
  · exact ((List.length_map ..).trans (supply_height _ _)).trans height.symm
  · exact fun e he => validInput e (valid e he) _

end SP1Clean.Export.InstalledAssembly
