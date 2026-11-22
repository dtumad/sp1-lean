import SP1Clean.Export.InstalledObservationPreset
import SP1Clean.Proofs.Completeness.MixedBumpInventory

/-! # Shared capacity of the two installed bump tables

Register window changes and noncanonical CPU-state pushes demand different tables. Their
padded rows both contribute to Byte, while each uses two entries of its own record channel.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Machine TraceGen Soundness FormalModel.Shard

private abbrev memory := providerTableFor (p := SP1Prime) .memoryBump
private abbrev state := providerTableFor (p := SP1Prime) .stateBump
private abbrev byteName := (Channels.byteChannel (p := SP1Prime)).name
private abbrev memoryName := (Channels.memoryChannel (p := SP1Prime)).name
private abbrev stateName := (Channels.stateChannel (p := SP1Prime)).name

private theorem bump_channels :
    rowChannelNames memory = [byteName, byteName, byteName, byteName, byteName, byteName, memoryName, memoryName] ∧
    rowChannelNames state = [stateName, stateName, byteName, byteName, byteName, byteName, byteName, byteName] := by
  constructor <;> rw [rowChannelNames, Component.interactions_eq]
  · change (((MemoryBumpChip.main (varFromOffset MemoryBumpChip.Inputs 0)).operations (size MemoryBumpChip.Inputs)).interactions.map _) = _
    simp only [MemoryBumpChip.main, circuit_norm, List.map_cons, List.map_nil]
  · change (((StateBumpChip.main (varFromOffset StateBumpChip.Inputs 0)).operations (size StateBumpChip.Inputs)).interactions.map _) = _
    simp only [StateBumpChip.main, circuit_norm, List.map_cons, List.map_nil]

/-- Actual demand generation pads the two refresh inventories independently. -/
theorem bump_targetHeight (s : WitnessGeneration.ComponentState Fp)
    (selected : s.component = providerTableFor .memoryBump ∨ s.component = providerTableFor .stateBump) :
    s.targetHeight = WitnessGeneration.demandHeight s.rows.size := by
  cases s with
  | mk component multiplicity operations interactions rows messages =>
    rcases selected with eq | eq <;> change component = _ at eq <;> subst component <;>
      exact WitnessGeneration.ComponentState.targetHeight_of_demand _ rfl

/-- Height contribution of the two demand-padded inventories in the installed assembly. -/
def bumpHeights (memoryRows stateRows : ℕ) (t : Component Fp) : ℕ :=
  slotRows memory (WitnessGeneration.demandHeight memoryRows) t +
    slotRows state (WitnessGeneration.demandHeight stateRows) t

/-- Exact occurrence counts of both installed bump tables, including zero-multiplicity padding. -/
theorem bump_occurrences (ctx : Context) (memoryRows stateRows : ℕ) (name : String) :
    let m := WitnessGeneration.demandHeight memoryRows
    let s := WitnessGeneration.demandHeight stateRows
    additionalOccurrences ctx (bumpHeights memoryRows stateRows) name =
      if name = byteName then 6 * (m + s)
      else if name = memoryName then 2 * m
      else if name = stateName then 2 * s else 0 := by
  obtain ⟨mem, cpu⟩ := bump_registered ctx
  have cost (table : Component Fp) : rowOccurrences table name = (rowChannelNames table).count name := by
    simp [rowOccurrences, rowChannelNames, List.count_eq_countP, List.countP_map, Function.comp_def]
  change additionalOccurrences ctx (fun t => slotRows memory _ t + slotRows state _ t) name = _
  rw [additionalOccurrences_add, additionalOccurrences_slot _ _ mem, additionalOccurrences_slot _ _ cpu,
    cost, cost, bump_channels.1, bump_channels.2]
  let m := WitnessGeneration.demandHeight memoryRows
  let s := WitnessGeneration.demandHeight stateRows
  by_cases b : name = byteName
  · subst name
    change m * 6 + s * 6 = 6 * (m + s)
    omega
  by_cases r : name = memoryName
  · subst name
    change m * 2 + s * 0 = 2 * m
    omega
  by_cases t : name = stateName
  · subst name
    change m * 0 + s * 2 = 2 * s
    omega
  · simp [b, r, t, Ne.symm b, Ne.symm r, Ne.symm t, byteName, memoryName, stateName] at *

/-- Reserved per-channel capacity for mixed paths with at most three register refreshes and
one CPU-state normalization per tape event. -/
def bumpBudget (name : String) : ℕ :=
  if name = byteName then 6 * (2 ^ 23 + 2 ^ 21)
  else if name = memoryName then 2 * 2 ^ 23
  else if name = stateName then 2 * 2 ^ 21 else 0

/-- The native event limit is shared by both tables; one ordinary instruction or ECALL supplies at most
three register refreshes and one CPU-state normalization. -/
theorem bump_occurrences_le (ctx : Context) {memoryRows stateRows count : ℕ}
    (mem : memoryRows ≤ 3 * count) (cpu : stateRows ≤ count) (bounded : count ≤ 2 ^ 21)
    (name : String) : additionalOccurrences ctx (bumpHeights memoryRows stateRows) name ≤ bumpBudget name := by
  have mh := WitnessGeneration.demandHeight_le_pow (show memoryRows ≤ 2 ^ 23 by omega)
  have sh := WitnessGeneration.demandHeight_le_pow (cpu.trans bounded)
  rw [bump_occurrences, bumpBudget]
  split <;> (repeat' split) <;> omega

private theorem bumpBudget_le (name : String) : bumpBudget name ≤ 6 * (2 ^ 23 + 2 ^ 21) := by
  unfold bumpBudget
  split <;> repeat' first | split | decide

/-- Shared capacity of the actual verifier and 44 installed tables. Both bump inventories are
constructed from the same mixed trace; the remaining allowance retains channel-specific costs. -/
theorem fixedProviderPreset_bump_capacity (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤
      SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 - 2 ^ 22 * ordinaryRowBound ch.name -
        observationBudget ch.name - bumpBudget ch.name) :
    ∃ inputs rows, routeBumpInputs? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some inputs ∧
      routeObservations? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          (observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t +
            (bumpHeights (MixedBumpInput.memoryRows inputs).length (MixedBumpInput.stateRows inputs).length t + other t)))) := by
  obtain ⟨inputs, route, _, mem, cpu, _⟩ := admissibleExecution_mixedBumpInventory execution
  let extra := bumpHeights (MixedBumpInput.memoryRows inputs).length (MixedBumpInput.stateRows inputs).length
  have bound : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx (fun t => extra t + other t) ch.name ≤
      SP1Prime - 1 - (2 ^ 30 + 1056) - 14 * 2 ^ 24 - 2 ^ 22 * ordinaryRowBound ch.name - observationBudget ch.name := by
    intro ch registered
    rw [additionalOccurrences_add]
    have used : additionalOccurrences ctx extra ch.name ≤ bumpBudget ch.name :=
      bump_occurrences_le ctx mem cpu (execution.work.1.trans preset.1) ch.name
    have left := remaining ch registered
    have maximum := bumpBudget_le ch.name
    have reserve := observation_reserve ch.name
    omega
  obtain ⟨rows, routed, count, fit⟩ := fixedProviderPreset_observation_capacity ctx execution preset _ bound
  exact ⟨inputs, rows, route, routed, count, fit⟩

/-- Every channel retains at least 222,297,056 occurrences beyond the verifier and these
44 physical slots. This includes both independently padded bump tables. -/
theorem fixedProviderPreset_bump_fit (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (other : Component Fp → ℕ)
    (remaining : ∀ ch ∈ (assembly ctx).channels, additionalOccurrences ctx other ch.name ≤ 222297056) :
    ∃ inputs rows, routeBumpInputs? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some inputs ∧
      routeObservations? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          (observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t +
            (bumpHeights (MixedBumpInput.memoryRows inputs).length (MixedBumpInput.stateRows inputs).length t + other t)))) := by
  apply fixedProviderPreset_bump_capacity ctx execution preset
  intro ch registered
  have reserve := observation_reserve ch.name
  have maximum := bumpBudget_le ch.name
  exact (remaining ch registered).trans (by omega)

/-- The constructed demands on the 44 covered tables and the actual verifier fit at the preset,
including arbitrary mixed ordinary and syscall normalization inputs. -/
theorem fixedProviderPreset_bump_base_fits (ctx : Context) {events : List ExecutionEvent}
    (execution : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) :
    ∃ inputs rows, routeBumpInputs? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some inputs ∧
      routeObservations? (policy SP1Prime ctx.image) ctx.image.program AccessFrontier.initial ctx.source.realize events = some rows ∧
      rows.length = events.countP ExecutionEvent.isOrdinary ∧ (assembly ctx).interactionsFit .logUp
        (physicalHeights ctx fun t => fixedHeight t + hintReadHeights events t + (ordinaryHeights rows t +
          (observationHeights ctx (events.countP ExecutionEvent.isOrdinary) t +
            bumpHeights (MixedBumpInput.memoryRows inputs).length (MixedBumpInput.stateRows inputs).length t))) := by
  simpa only [Nat.add_zero] using fixedProviderPreset_bump_fit ctx execution preset (fun _ => 0)
    (by intro ch registered; simp [additionalOccurrences])

end SP1Clean.Export.InstalledAssembly
