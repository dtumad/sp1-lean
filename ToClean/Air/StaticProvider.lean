module

public import ToClean.Air.FixedPrefix
public import ToClean.Air.FixedRows
public import ToClean.Air.ChannelClosure
public import ToClean.Air.Authentication
public import Clean.Circuit.WitnessIRSugar
public import Clean.Utils.Tactics
public import Clean.Utils.Tactics.ProvableStructDeriving
public import Mathlib.Data.Nat.Log

/-! # Fixed-column providers for static membership

Clean has static lookup predicates and verifier-fixed column programs, but no typed bridge
between them. This adapter supplies the original predicate through a channel whose provider
rows have verifier-fixed messages and prover-owned multiplicities. A fixed eligibility flag
distinguishes real requests from padding and duplicate rows without changing Clean's scheduler.
Every original row remains in order; only the first copy may carry demand. Empty tables have
one inactive row, and other tables round up to a power of two. It reuses Clean's row IR and
component assumptions; witness scheduling and Rust lowering remain upstream operations.
Delete this addition when Clean supplies the corresponding static-provider API.
-/

@[expose] public section

namespace StaticTable

open Circuit Air.Flat

variable {F : Type} [FiniteField F] {Row : TypeMap} [ProvableType Row]

/-- Membership messages keep their fixed eligibility tag distinct from the payload. A named
carrier also avoids overlapping scalar-pair ProvableType instances when `Row = field`. -/
structure Entry (Row : TypeMap) (F : Type) where
  /-- Original static-table value, retained even on duplicate rows. -/
  payload : Row F
  /-- Fixed authorization flag: one only on the first occurrence of an original payload. -/
  eligible : F
deriving ProvableStruct

/-- Evaluating a tagged entry preserves the original payload's own provable representation. -/
theorem Entry.eval_payload (env : Environment F) (entry : Var (Entry Row) F) :
    (ProvableStruct.eval env entry).payload = eval env entry.payload := by
  cases entry
  rfl

/-- The channel carries the original static predicate, independently of committed prover data. -/
def channel (table : StaticTable F Row) : Channel F (Entry Row) where
  name := table.name
  Guarantees row _ := row.eligible = 1 ∧ table.Spec row.payload

/-- The smallest backend trace height retaining every original row, including an empty table. -/
def height (table : StaticTable F Row) : ℕ := 2 ^ Nat.clog 2 table.length

omit [FiniteField F] in
theorem length_le_height (table : StaticTable F Row) : table.length ≤ table.height :=
  Nat.le_pow_clog (by decide) _

omit [FiniteField F] in
theorem height_pos (table : StaticTable F Row) : 0 < table.height := by
  exact pow_pos (by decide) _

omit [FiniteField F] in
/-- Padding has an explicit expansion bound; capacity proofs must still account for it. -/
theorem height_lt_double (table : StaticTable F Row) :
    table.height < 2 * max table.length 1 := by
  by_cases small : table.length ≤ 1
  · simp [height, Nat.clog_of_right_le_one small, max_eq_right small]
  · have large : 1 < table.length := by omega
    have positive := Nat.clog_pos (by decide : 1 < 2) large
    have lower := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) large
    unfold height
    rw [← Nat.succ_pred_eq_of_pos positive, pow_succ, max_eq_left (by omega)]
    omega

/-- Retain duplicate payloads, but authorize only their first occurrence. Padding carries a
zero payload and a distinct, inactive channel tag, so it cannot alias a real zero request. -/
def fixedEntry (table : StaticTable F Row) (index : ℕ) : Entry Row F :=
  if bound : index < table.length then
    let row := table.row ⟨index, bound⟩
    let repeated := (List.range index).any fun prior =>
      if h : prior < table.length then toElements (table.row ⟨prior, h⟩) == toElements row
      else false
    ⟨row, if repeated then 0 else 1⟩
  else ⟨fromElements (Vector.replicate (size Row) 0), 0⟩

/-- Eligibility is authenticated by fixed columns, independently of prover multiplicities. -/
theorem fixedEntry_spec (table : StaticTable F Row) (index : ℕ)
    (eligible : (table.fixedEntry index).eligible ≠ 0) :
    (table.fixedEntry index).eligible = 1 ∧ table.Spec (table.fixedEntry index).payload := by
  unfold fixedEntry at eligible ⊢
  split
  next bound =>
    dsimp only at eligible ⊢
    simp only [dif_pos bound] at eligible
    split
    · rename_i repeated
      simp [repeated] at eligible
    · exact ⟨rfl, (table.contains_iff _).mp ⟨⟨index, bound⟩, rfl⟩⟩
  next bound => simp [dif_neg bound] at eligible

/-- Padding and duplicate eligibility preserve exactly the original membership predicate.
This is a fixed-table coverage theorem, not completeness of the ensemble scheduler. -/
theorem spec_iff_fixedEntry (table : StaticTable F Row) (row : Row F) :
    table.Spec row ↔ ∃ index : Fin table.height,
      (table.fixedEntry index.val).payload = row ∧ (table.fixedEntry index.val).eligible = 1 := by
  classical
  constructor
  · intro member
    obtain ⟨original, equal⟩ := (table.contains_iff row).mpr member
    have existsIndex : ∃ index : ℕ, ∃ bound : index < table.length,
        row = table.row ⟨index, bound⟩ := ⟨original.val, original.isLt, equal⟩
    obtain ⟨bound, equal⟩ := Nat.find_spec existsIndex
    have notRepeated : ((List.range (Nat.find existsIndex)).any fun prior =>
        if h : prior < table.length then
          toElements (table.row ⟨prior, h⟩) == toElements (table.row ⟨Nat.find existsIndex, bound⟩)
        else false) = false := by
      apply Bool.eq_false_iff.mpr
      intro repeated
      obtain ⟨prior, earlier, same⟩ := List.any_eq_true.mp repeated
      have before := List.mem_range.mp earlier
      have priorBound : prior < table.length := lt_trans before bound
      simp only [dif_pos priorBound, beq_iff_eq] at same
      have payload := congrArg (fromElements (M := Row)) same
      simp only [ProvableType.fromElements_toElements] at payload
      have minimal := Nat.find_min' existsIndex ⟨priorBound, equal.trans payload.symm⟩
      omega
    refine ⟨⟨Nat.find existsIndex, lt_of_lt_of_le bound table.length_le_height⟩, ?_, ?_⟩
    · simpa only [fixedEntry, dif_pos bound] using equal.symm
    · simp only [fixedEntry, dif_pos bound, notRepeated, Bool.false_eq_true, ↓reduceIte]
  · rintro ⟨index, equal, eligible⟩
    have valid := table.fixedEntry_spec index.val (by rw [eligible]; exact one_ne_zero)
    simpa only [equal] using valid.2

/-- Enumerate the typed table through Clean's index-aware fixed-column IR. -/
def fixedColumns (table : StaticTable F Row) (bounded : table.height < UInt64.size) : FixedColumns F :=
  FixedColumns.ofRows (Vector.ofFn fun index : Fin table.height =>
    toElements (table.fixedEntry index.val)) bounded

/-- Fixed columns are exactly the message prefix; multiplicities remain committed columns. -/
@[simp] theorem fixedColumns_width (table : StaticTable F Row) (bounded : table.height < UInt64.size) :
    (table.fixedColumns bounded).width = size (Entry Row) := rfl

/-- Fixed columns already have their final physical height before witness generation. -/
@[simp] theorem fixedColumns_height (table : StaticTable F Row) (bounded : table.height < UInt64.size) :
    (table.fixedColumns bounded).height.toNat = table.height := rfl

/-- The canonical row program realizes every enumerated row without a native witness closure. -/
theorem fixedColumns_row (table : StaticTable F Row) (bounded : table.height < UInt64.size)
    (index : Fin table.height) :
    (table.fixedColumns bounded).row (UInt64.ofNat index.val) = (toElements (table.fixedEntry index.val)).toArray := by
  simp [fixedColumns, FixedColumns.ofRows_row]

/-- A membership provider emits the authenticated message at its supplied multiplicity.
The fixed prefix authenticates eligibility; inactive rows must have zero multiplicity. -/
def provider (table : StaticTable F Row) :
    GeneralFormalCircuit F (ProvablePair (Entry Row) field) unit where
  name := table.name ++ ".provider"
  main input := do
    assertZero ((1 - input.1.eligible) * input.2)
    table.channel.emit input.2 input.1
  Assumptions input _ := input.1.eligible ≠ 0 → input.1.eligible = 1 ∧ table.Spec input.1.payload
  Spec input _ _ := input.2 ≠ 0 → table.Spec input.1.payload
  ProverAssumptions input _ _ := input.2 = 0 ∨ input.1.eligible = 1
  channelsWithRequirements := [table.channel.toRaw]
  soundness := by
    circuit_proof_start [channel]
    rw [← h_input] at h_assumptions ⊢
    dsimp only at h_assumptions ⊢
    have active : Expression.eval env input_var.2 ≠ 0 →
        (ProvableStruct.eval env input_var.1).eligible = 1 := by
      intro counted
      have := (mul_eq_zero.mp h_holds).resolve_right counted
      exact (sub_eq_zero.mp this).symm
    have valid : Expression.eval env input_var.2 ≠ 0 →
        (ProvableStruct.eval env input_var.1).eligible = 1 ∧
          table.Spec (ProvableStruct.eval env input_var.1).payload := by
      intro counted
      exact h_assumptions (by rw [active counted]; exact one_ne_zero)
    exact ⟨fun counted => (valid counted).2, fun _ counted => valid counted⟩
  completeness := by
    circuit_proof_start [channel]
    rw [← h_input] at h_assumptions
    rcases h_assumptions with zero | active
    · dsimp only at zero
      rw [zero, mul_zero]
    · dsimp only at active
      rw [active, sub_self, zero_mul]

/-- Membership follows from the verifier-fixed prefix, with no residual provider-validity
assumption on the ensemble or its caller. Counts are the only prover-owned input cells. -/
def component (table : StaticTable F Row) (bounded : table.height < UInt64.size) : Component F where
  circuit := table.provider
  fixedColumns := some (table.fixedColumns bounded)
  Assumptions _ _ := True
  circuit_assumptions_of_assumptions := by
    intro index input data fixed _ _
    have bound : index.toNat < table.height := (fixed (table.fixedColumns bounded) (by simp)).1
    have fixedCells := fixed.input_prefix (by rfl)
    have rowEq := table.fixedColumns_row bounded ⟨index.toNat, bound⟩
    simp only [UInt64.ofNat_toNat] at rowEq
    rw [rowEq] at fixedCells
    have decoded := congrArg (fromElements (M := Entry Row)) (Vector.toArray_inj.mp fixedCells)
    simp only [ProvableType.fromElements_toElements] at decoded
    change input.1.eligible ≠ 0 → input.1.eligible = 1 ∧ table.Spec input.1.payload
    rw [decoded]
    exact table.fixedEntry_spec index.toNat
  fixed_width_le_input := by
    change size (Entry Row) ≤ size (Entry Row) + 1
    omega

/-- Authenticate every membership pull from the actual fixed provider and the complete balanced
ledger. Other components may consume this channel, but cannot declare it as an outgoing requirement.
The fixed provider's semantic assumptions follow from its physical prefix and canonical data. -/
theorem guarantees_of_balance (table : StaticTable F Row) (bounded : table.height < UInt64.size)
    {Public : TypeMap} [ProvableType Public] {ensemble : Ensemble F Public}
    (witness : EnsembleWitness ensemble) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannel table.channel.toRaw)
    (verifier : ensemble.VerifierChannelRequirements witness.publicInput witness.data table.channel.toRaw)
    (sources : ∀ component ∈ ensemble.tables, component = table.component bounded ∨
      table.channel.toRaw ∉ component.circuit.channelsWithRequirements) :
    ensemble.VerifierChannelGuarantees witness.publicInput witness.data table.channel.toRaw ∧
      ∀ physical ∈ witness.tables, physical.ChannelGuarantees table.channel.toRaw := by
  apply witness.channelGuarantees_of_requirements table.channel.toRaw balanced verifier
  intro physical member
  rcases sources physical.component (EnsembleWitness.component_mem_tables_of_mem member) with fixed | silent
  · have assumptions : physical.Assumptions := by
      intro row _
      change physical.component.Assumptions _ _
      rw [fixed]
      trivial
    intro row rowMember interaction emitted _
    exact (physical.component.weakSoundness_of_no_guarantees (by rw [fixed]; rfl)
      (physical.circuitAssumptions_of_dataConsistency (witness.dataConsistency_of_mem physical member)
        assumptions row rowMember)
      (constraints physical member row rowMember)).2 interaction emitted
  · intro row rowMember
    exact Operations.requirements_of_not_mem _ _ _
      (physical.component.inChannelsOrRequirements_of_constraints _
        (constraints physical member row rowMember)) _ silent

/-- Emit original payloads on an existing semantic channel. Eligibility stays in the fixed
prefix, so consumers need neither a second membership channel nor an eligibility field. -/
def payloadProvider (table : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ row, table.Spec row → ∀ data, target.Guarantees row data) :
    GeneralFormalCircuit F (ProvablePair (Entry Row) field) unit where
  name := target.name ++ ".source"
  main input := do
    assertZero ((1 - input.1.eligible) * input.2)
    target.emit input.2 input.1.payload
  Assumptions input _ := input.1.eligible ≠ 0 → input.1.eligible = 1 ∧ table.Spec input.1.payload
  Spec input _ _ := input.2 ≠ 0 → table.Spec input.1.payload
  ProverAssumptions input _ _ := input.2 = 0 ∨ input.1.eligible = 1
  channelsWithRequirements := [target.toRaw]
  soundness := by
    circuit_proof_start
    rw [← h_input] at h_assumptions ⊢
    dsimp only at h_assumptions ⊢
    have active : Expression.eval env input_var.2 ≠ 0 →
        (ProvableStruct.eval env input_var.1).eligible = 1 := by
      intro counted
      exact (sub_eq_zero.mp ((mul_eq_zero.mp h_holds).resolve_right counted)).symm
    have member : Expression.eval env input_var.2 ≠ 0 →
        table.Spec (ProvableStruct.eval env input_var.1).payload := by
      intro counted
      exact (h_assumptions (by rw [active counted]; exact one_ne_zero)).2
    exact ⟨member, fun _ counted => valid _ (member counted) _⟩
  completeness := by
    circuit_proof_start
    rw [← h_input] at h_assumptions
    rcases h_assumptions with zero | active
    · dsimp only at zero
      rw [zero, mul_zero]
    · dsimp only at active
      rw [active, sub_self, zero_mul]

/-- Publish fixed payloads at prover-owned counts. Physical preprocessing discharges all
semantic source assumptions; inactive and repeated rows remain present with zero counts. -/
def payloadComponent (table : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ row, table.Spec row → ∀ data, target.Guarantees row data)
    (bounded : table.height < UInt64.size) : Component F where
  circuit := table.payloadProvider target valid
  fixedColumns := some (table.fixedColumns bounded)
  Assumptions _ _ := True
  circuit_assumptions_of_assumptions := by
    intro index input data fixed _ _
    have bound : index.toNat < table.height := (fixed (table.fixedColumns bounded) (by simp)).1
    have fixedCells := fixed.input_prefix (by rfl)
    have rowEq := table.fixedColumns_row bounded ⟨index.toNat, bound⟩
    simp only [UInt64.ofNat_toNat] at rowEq
    rw [rowEq] at fixedCells
    have decoded := congrArg (fromElements (M := Entry Row)) (Vector.toArray_inj.mp fixedCells)
    simp only [ProvableType.fromElements_toElements] at decoded
    change input.1.eligible ≠ 0 → input.1.eligible = 1 ∧ table.Spec input.1.payload
    rw [decoded]
    exact table.fixedEntry_spec index.toNat
  fixed_width_le_input := by
    change size (Entry Row) ≤ size (Entry Row) + 1
    omega

/-- Source authenticity uses the actual table's fixed prefix and canonical data, rather than
assuming arbitrary prover-selected environments already contain authenticated payloads. -/
theorem payload_authenticates (table : StaticTable F Row) (target : Channel F Row)
    (valid : ∀ row, table.Spec row → ∀ data, target.Guarantees row data)
    (bounded : table.height < UInt64.size) (physical : Table F)
    (same : physical.component = table.payloadComponent target valid bounded)
    (consistent : physical.DataConsistency) (constraints : physical.Constraints) :
    physical.Authenticates target table.Spec := by
  have assumptions : physical.Assumptions := by
    intro row _
    change physical.component.Assumptions _ _
    rw [same]
    trivial
  intro row rowMember interaction emitted active _
  have sound := (physical.component.weakSoundness_of_no_guarantees (by rw [same]; rfl)
    (physical.circuitAssumptions_of_dataConsistency consistent assumptions row rowMember)
    (constraints row rowMember)).1
  rw [same] at sound emitted
  change (valueFromOffset (ProvablePair (Entry Row) field) 0 (physical.environment row)).2 ≠ 0 →
    table.Spec (valueFromOffset (ProvablePair (Entry Row) field) 0 (physical.environment row)).1.payload at sound
  rw [Operations.interactionValuesWith, Component.interactionsWith_eq] at emitted
  change interaction ∈ ((((table.payloadProvider target valid).main
    (varFromOffset (ProvablePair (Entry Row) field) 0)).operations
    (size (ProvablePair (Entry Row) field))).interactionsWith target.toRaw).map _ at emitted
  have interactions (input : Var (ProvablePair (Entry Row) field) F) (offset : ℕ) :
      (((table.payloadProvider target valid).main input).operations offset).interactionsWith
        target.toRaw = [(target.pushedIf input.2 input.1.payload).toRaw] := by
    simp [payloadProvider, circuit_norm]
  rw [interactions, List.map_cons, List.map_nil] at emitted
  obtain rfl := List.mem_singleton.mp emitted
  have evaluated := Channel.eval_pushedIf (channel := target)
    (enabled := (varFromOffset (ProvablePair (Entry Row) field) 0).2)
    (msg := (varFromOffset (ProvablePair (Entry Row) field) 0).1.payload)
    (env := physical.environment row)
  have inputEq := eval_varFromOffset_valueFromOffset (F := F)
    (ProvablePair (Entry Row) field) 0 (physical.environment row)
  simp only [CircuitType.eval_provablePair_dispatch] at inputEq
  refine ⟨_, (congrArg Interaction.msg evaluated).trans ?_, sound ?_⟩
  · have payload := congrArg (fun input : ProvablePair (Entry Row) field F =>
      (toElements input.1.payload).toArray) inputEq
    simpa only [Channel.pushedIfValue, ProvableStruct.eval_eq_eval, Entry.eval_payload] using payload
  · rw [(congrArg Interaction.mult evaluated).trans (congrArg Prod.snd inputEq)] at active
    exact active

end StaticTable
