import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.CoreExecutionRow
import SP1Clean.Soundness.MemoryFrontier

/-! # Shared physical ledger projections

These component and list lemmas retain physical occurrences and shared prover data independently
of the enclosing ensemble's source policy. Both boot and local adapters use them; ordering itself
remains the common `StateChronology` argument.
-/

namespace SP1Clean.Soundness.NativeCore

open Circuit Air.Flat SP1Clean.Channels SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

omit [Fact (2 ^ 24 < p)] in
theorem typedTableInteractions_nil {Message : TypeMap} [ProvableType Message]
    (table : Table (ZMod p)) (channel : Channel (ZMod p) Message)
    (silent : channel.toRaw ∉ table.component.circuit.channels) :
    typedTableInteractionsWith table channel = [] := by
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw, List.map_nil]
  exact table.interactionsWith_nil_of_channel_not_mem silent

/-- Every component in the fixed Byte/Range batch is silent on other channels. -/
theorem byteProvider_channel_silent (component : Component (ZMod p))
    (member : component ∈ (sp1ProviderTables (p := p)).take 23)
    (channel : RawChannel (ZMod p)) (different : channel ≠ byteChannel.toRaw) :
    channel ∉ component.circuit.channels := by
  rw [sp1ProviderTables, ← List.map_take] at member
  obtain ⟨id, idMem, rfl⟩ := List.mem_map.mp member
  have prefixEq : ProviderTableId.all.take 23 =
      ByteProviderId.all.map .byte ++ (List.finRange 17).map .range := by decide
  rw [prefixEq] at idMem
  rcases List.mem_append.mp idMem with byte | range
  · obtain ⟨provider, _, rfl⟩ := List.mem_map.mp byte
    cases provider <;> change channel ∉ [byteChannel.toRaw]
    all_goals simpa
  · obtain ⟨width, _, rfl⟩ := List.mem_map.mp range
    change channel ∉ [byteChannel.toRaw]
    simpa

theorem flatMap_split {α β : Type*} (items : List α) (f : α → List β) (start count : ℕ) :
    (items.drop start).flatMap f = ((items.drop start).take count).flatMap f ++
      (items.drop (start + count)).flatMap f := by
  have split := congrArg (List.flatMap f) (List.take_append_drop count (items.drop start))
  simpa only [List.flatMap_append, List.drop_drop, Nat.add_comm] using split.symm

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem flatMap_filter_inactive {α β : Type*} (rows : List α) (keep : α → Bool)
    (f : α → List β) (inactive : ∀ row ∈ rows, keep row = false → f row = []) :
    (rows.filter keep).flatMap f = rows.flatMap f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have rest := ih (fun item member => inactive item (List.mem_cons_of_mem _ member))
    cases active : keep row
    · simp [active, rest, inactive row List.mem_cons_self active]
    · simp [active, rest]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem pushesAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pushesAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (·.memPushes)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pushesAt, Multiset.filter_coe, rowPushesAt]

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
theorem pullsAt_flatMap (rows : List (RowFacts p)) (loc : MemLoc) :
    pullsAt rows loc = Multiset.filter (fun message => MemoryMsg.locOf message = loc)
      (↑(rows.flatMap (fun row => row.memPulls.map Prod.fst)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [filter_coe_flatMap]
  simp only [pullsAt, Multiset.filter_coe, rowPullsAt]

omit [Fact (2 ^ 24 < p)] in
/-- A verifier preserving the standard State interactions emits exactly the two public endpoints. -/
theorem verifier_state_interactions_of_main {assembly : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness assembly)
    (main : ∀ input offset, ((assembly.verifier.main input).operations offset).interactionsWith stateChannel.toRaw =
      ((sp1StateVerifierMain input).operations offset).interactionsWith stateChannel.toRaw) :
    typedTableInteractionsWith witness.verifierTable stateChannel =
      [TypedInteraction.pulledIfValue stateChannel 1 (finalBoundaryStateMessage witness.publicInput),
       TypedInteraction.pushedIfValue stateChannel 1 (initialBoundaryStateMessage witness.publicInput)] := by
  have inputEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)) = witness.publicInput :=
    ProvableType.eval_fromInput_varFromOffset_zero witness.publicInput witness.data
  have finalEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_clk_high,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_clk_low,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc0,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc1,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).final_pc2⟩ :
        StateMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.final_clk_high, witness.publicInput.final_clk_low,
        witness.publicInput.final_pc0, witness.publicInput.final_pc1,
        witness.publicInput.final_pc2⟩ : StateMsg (ZMod p)) := by
    rw [eval_finalBoundaryStateMessage, inputEval]
  have initialEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_clk_high,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_clk_low,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc0,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc1,
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).init_pc2⟩ :
        StateMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.init_clk_high, witness.publicInput.init_clk_low,
        witness.publicInput.init_pc0, witness.publicInput.init_pc1,
        witness.publicInput.init_pc2⟩ : StateMsg (ZMod p)) := by
    rw [eval_initialBoundaryStateMessage, inputEval]
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw]
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromInput witness.publicInput witness.data))
      (((assembly.verifier.main
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p))).operations
          (size SP1PublicIO)).interactionsWith stateChannel.toRaw) = _
  rw [main, sp1StateVerifierMain_stateInteractions]
  simp only [List.map_cons, List.map_nil]
  rw [Channel.eval_pulled, Channel.eval_pushed, finalEval, initialEval]
  rfl

end SP1Clean.Soundness.NativeCore
