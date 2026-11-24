import SP1Clean.Soundness.WriteSourceRows

/-! # Every genuine predecessor pull publishes its WRITE supply record

Recover the exact physical source occurrence in the reverse direction, including repeated
register aliases. The source uses the accessing row's own clock for its upper endpoint.
-/

namespace SP1Clean.WriteProbe.AccessInventory
open Circuit Air.Flat Soundness Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Evaluate expressions using the registered instruction's exact input representation. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Inputs :=
  (supportedChipFor (p := p) id).kind.provableInputs

/-- Use the output columns installed by the same instruction registry. -/
local instance (id : InstructionChipId) : ProvableType (supportedChipFor (p := p) id).kind.Cols :=
  (supportedChipFor (p := p) id).kind.provableCols

omit [Fact (2 ^ 25 < p)] in
private theorem pull_eq {w w' : ZMod p} {r r' : MemoryMsg (ZMod p)}
    (eq : memoryChannel.pulledIfValue w r = memoryChannel.pulledIfValue w' r') :
    w = w' ∧ r = r' := by
  exact ⟨congrArg Interaction.mult eq, ProvableType.toElements_inj_iff.mp (Vector.toArray_inj.mp (congrArg Interaction.msg eq))⟩

/-- Every original ordinary Memory pull has a private source on the same row. -/
theorem ordinary_records_of_pull (id : InstructionChipId) (env : Environment (ZMod p))
    (weight : ZMod p) (prior : MemoryMsg (ZMod p))
    (occurs : memoryChannel.pulledIfValue weight prior ∈ (original (.ordinary id)).operations.interactionValuesWith memoryChannel.toRaw env) :
    let input := varFromOffset (supportedChipFor (p := p) id).kind.Inputs 0
    (weight, AccessSupply.readback (eval env ((OrdinarySources.layout id).incoming input)) prior) ∈ rowRecords (.ordinary id) env := by
  change _ ∈ (ProtectedOrdinaryReceipt.component id).operations.interactionValuesWith memoryChannel.toRaw env at occurs
  simp only [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions id (memoryChannel (p := p)).toRaw (by
    intro same; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") same)),
    ProtectedOrdinaryReceipt.provider_interactions id (memoryChannel (p := p)).toRaw (by
    intro same; exact Bool.noConfusion (congrArg (fun c => c.name == "SP1Memory") same)),
    Component.interactionsWith_eq, Component.rowOperations] at occurs
  change _ ∈ ((((supportedChipFor (p := p) id).circuit.main (varFromOffset _ 0)).operations
    (size (supportedChipFor (p := p) id).kind.Inputs)).interactionsWith memoryChannel.toRaw).map (AbstractInteraction.eval env) at occurs
  simp only [OrdinarySources.original_memory, List.map_map, Function.comp_def] at occurs
  obtain ⟨site, member, equal⟩ := List.mem_map.mp occurs
  have direction : site.direction = .pull := congrArg Interaction.direction equal
  have evaluated := OrdinarySources.evaluated_pull env site direction
  obtain ⟨gate, value⟩ := pull_eq (evaluated.symm.trans equal)
  exact List.mem_map.mpr ⟨site, List.mem_filter.mpr ⟨member, beq_iff_eq.mpr direction⟩,
    Prod.ext gate (congrArg (AccessSupply.readback _) value)⟩

omit [Fact (2 ^ 25 < p)] in
private theorem typed_pull (env : Environment (ZMod p)) (gate : Expression (ZMod p)) (msg : Var MemoryMsg (ZMod p)) :
    (⟨.pull, gate, msg⟩ : ChannelInteraction (memoryChannel (p := p))).toRaw.eval env =
      memoryChannel.pulledIfValue (env gate) (eval env msg) :=
  OrdinarySources.evaluated_pull env ⟨.pull, gate, msg⟩ rfl

/-- Filtering the native host Memory ledger retains exactly its physical predecessor sites. -/
theorem host_pulls (family : HostSources.Family) (env : Environment (ZMod p)) :
    let input := varFromOffset (HostSources.original (p := p) family).Input 0
    let offset := size (HostSources.original (p := p) family).Input
    ((HostSources.original family).operations.interactionValuesWith memoryChannel.toRaw env).filter
      (fun i => i.direction == .pull) =
      (HostSources.sites family).map fun site =>
        memoryChannel.pulledIfValue (env (site.gate input offset)) (eval env (site.message input offset)) := by
  cases family with
  | ecall =>
    rw [show (HostSources.original (p := p) .ecall).operations.interactionValuesWith memoryChannel.toRaw env = _ from
      HostCallProjection.memory_values env]
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change (((((SyscallInstrsChip.main (p := p) (varFromOffset SyscallInstrsChip.Inputs 0)).operations
      (size SyscallInstrsChip.Inputs)).interactionsWith memoryChannel.toRaw).map (AbstractInteraction.eval env)).filter _) = _
    rw [SyscallInstrsChip.Ledger.syscallInstrsInteractionsWith_memory]
    simp only [HostSources.sites, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil,
      AbstractInteraction.eval_direction, ChannelInteraction.toRaw_direction, beq_self_eq_true,
      show (Channel.Direction.push == .pull) = false by rfl, Bool.false_eq_true, ↓reduceIte, typed_pull, Channel.pulledIfValue]
    rfl
  | word last =>
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change ((((HintReadWordChip.circuit (p := p) last).main (varFromOffset HintReadWordChip.RowInput 0)).operations
      (size HintReadWordChip.RowInput)).interactionValuesWith memoryChannel.toRaw env).filter _ = _
    rw [HintReadWordChip.guarded_memory_values]
    simp only [HostSources.sites, List.map_cons, List.map_nil, List.filter_cons, List.filter_nil,
      Channel.pulledIfValue, Channel.pushedIfValue, beq_self_eq_true,
      show (Channel.Direction.push == .pull) = false by rfl, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The three ECALL predecessor accesses and both HINT_READ word variants also publish
every original pull, at the exact physical host clock. -/
theorem host_records_of_pull (family : HostSources.Family) (env : Environment (ZMod p))
    (weight : ZMod p) (prior : MemoryMsg (ZMod p))
    (occurs : memoryChannel.pulledIfValue weight prior ∈ (HostSources.original family).operations.interactionValuesWith memoryChannel.toRaw env) :
    (weight, AccessSupply.atClock (HostSources.upper family env) prior) ∈ rowRecords (.host family) env := by
  have filtered : memoryChannel.pulledIfValue weight prior ∈
      ((HostSources.original family).operations.interactionValuesWith memoryChannel.toRaw env).filter
        (fun i => i.direction == .pull) := List.mem_filter.mpr ⟨occurs, rfl⟩
  rw [host_pulls] at filtered
  obtain ⟨site, used, equal⟩ := List.mem_map.mp filtered
  obtain ⟨gate, value⟩ := pull_eq equal
  apply List.mem_map.mpr
  refine ⟨site, used, Prod.ext gate ?_⟩
  simp only [AccessSupply.eval_atClock, value, HostSources.upper]

/-- The register-refresh row yields its full preceding word through the actual read-back
timestamp, including that endpoint. -/
theorem refresh_records_of_pull (env : Environment (ZMod p)) (weight : ZMod p) (prior : MemoryMsg (ZMod p))
    (occurs : memoryChannel.pulledIfValue weight prior ∈ (original .refresh).operations.interactionValuesWith memoryChannel.toRaw env) :
    let row := valueFromOffset MemoryBumpChip.Inputs 0 env
    let version := refreshReadback row
    (weight, AccessSupply.atClock (version.currentHigh, version.currentLow) prior) ∈ rowRecords .refresh env := by
  let input := varFromOffset (F := ZMod p) MemoryBumpChip.Inputs 0
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations] at occurs
  change _ ∈ ((((MemoryBumpChip.main input).operations (size MemoryBumpChip.Inputs)).interactionsWith memoryChannel.toRaw).map
    (AbstractInteraction.eval env)) at occurs
  rw [memoryBumpMain_memoryInteractions] at occurs
  simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false, Channel.eval_pulledIf,
    Channel.eval_pushedIf, ProvableType.eval_field, eval_memoryBump_pulledMsg, input, eval_varFromOffset_valueFromOffset] at occurs
  rcases occurs with pulled | pushed
  · obtain ⟨gate, rfl⟩ := pull_eq pulled
    simp only [rowRecords, List.mem_singleton]
    refine Prod.ext ?_ rfl
    simpa only [← eval_varFromOffset_valueFromOffset, circuit_norm] using gate
  · exact False.elim (Channel.Direction.noConfusion (congrArg Interaction.direction pushed))

/-- Both original finalizers publish the full suffix of the very Memory record they consume. -/
theorem final_records_of_pull (ram : Bool) (env : Environment (ZMod p)) (weight : ZMod p) (prior : MemoryMsg (ZMod p))
    (occurs : memoryChannel.pulledIfValue weight prior ∈ (original (.finalizer ram)).operations.interactionValuesWith memoryChannel.toRaw env) :
    (weight, finalReadback prior) ∈ rowRecords (.finalizer ram) env := by
  simp only [original, original_final_memory_values, List.mem_singleton] at occurs
  obtain ⟨gate, msg⟩ := pull_eq occurs
  simp only [rowRecords, List.mem_singleton]
  rw [gate, msg]

/-- The last eligible incoming clock comes from this particular physical source:
ordinary or host incoming clock, refresh installation time, or the final 48-bit suffix. -/
noncomputable def upper (id : Source) (env : Environment (ZMod p)) : ZMod p × ZMod p :=
  match id with
  | .ordinary instruction =>
    let state := eval env ((OrdinarySources.layout (p := p) instruction).incoming (varFromOffset _ 0))
    (state.clk_high, state.clk_low)
  | .host family => HostSources.upper family env
  | .refresh =>
    let r := refreshReadback (valueFromOffset MemoryBumpChip.Inputs 0 env)
    (r.currentHigh, r.currentLow)
  | .finalizer _ => (16777215, 16777215)

/-- Total publication from all 31 registered source families. Any actual Memory pull has
the very same gate, key, old word and prior timestamp on the complete physical source tape. -/
theorem records_of_pull (raw : Source → Table (ZMod p)) (registered : ∀ id, (raw id).component = original id)
    (id : Source) (physical : Array (ZMod p)) (member : physical ∈ (raw id).table)
    (weight : ZMod p) (prior : MemoryMsg (ZMod p))
    (pull : memoryChannel.pulledIfValue weight prior ∈ (raw id).component.operations.interactionValuesWith
      memoryChannel.toRaw ((raw id).environment physical)) :
    (weight, AccessSupply.atClock (upper id ((raw id).environment physical)) prior) ∈ records raw := by
  rw [registered] at pull
  apply List.mem_flatMap.mpr
  refine ⟨id, sources_complete id, List.mem_flatMap.mpr ⟨physical, member, ?_⟩⟩
  cases id with
  | ordinary instruction => exact ordinary_records_of_pull instruction _ weight prior pull
  | host family => exact host_records_of_pull family _ weight prior pull
  | refresh => exact refresh_records_of_pull _ weight prior pull
  | finalizer ram => exact final_records_of_pull ram _ weight prior pull

end SP1Clean.WriteProbe.AccessInventory
