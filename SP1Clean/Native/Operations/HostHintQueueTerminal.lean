import SP1Clean.Native.Operations.HintQueueBoundary
import Clean.Gadgets.Bits
import ToClean.Circuit.InteractionRecovery
import ToClean.Air.LookupFree
import ToClean.Air.ChannelClosure

/-! # A private timestamp at the outgoing hint cursor

One verifier-fixed row receives both target pointers at a privately supplied timestamp.
It re-emits them at the clock of the public endpoint. Its fixed height and ticket make
the transfer occur once, even if the private cursor is identical to the public cursor.
-/

namespace SP1Clean.HostHintQueueTerminal

open Circuit Air.Flat HostHintQueue
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The fixed ticket, its scheduled multiplicity and two private timestamp limbs. -/
structure Inputs (F : Type) where
  /-- The unique fixed cell marking the terminal row. -/
  ticket : F
  /-- Multiplicity generated for the public outgoing cursor. -/
  count : F
  /-- High 24 bits of the privately witnessed last hint timestamp. -/
  high : F
  /-- Low 24 bits of the privately witnessed last hint timestamp. -/
  low : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Physical component name and key of the two-column private input. -/
def tableName := "sp1.native.hint_queue.terminal"

/-- Substituting the private clock preserves both authenticated pointer vectors. -/
def cursor {F : Type} (target : State F) (high low : F) : State F :=
  { target with clk_high := high, clk_low := low }

/-- The terminal transfers one cursor at a 48-bit clock. -/
def Valid (input : Inputs (ZMod p)) : Prop :=
  input.ticket = 1 ∧ input.count = input.ticket ∧ input.high.val < 2 ^ 24 ∧ input.low.val < 2 ^ 24

omit [Fact p.Prime] in
private theorem limbBound : 2 ^ 24 < p := by have := Fact.out (p := 2 ^ 25 < p); omega

/-- Check the ticket and clock limbs and transfer the cursor between its two timestamps. -/
def main (target : State (ZMod p)) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.ticket - 1)
  assertZero (input.count - input.ticket)
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.high
  assertion (Gadgets.ToBits.rangeCheck 24 limbBound) input.low
  stateChannel.pull (cursor (const target) input.high input.low)
  stateChannel.pushIf input.count (const target)

/-- Checked one-row transfer of the authenticated outgoing hint pointers. -/
def circuit (target : State (ZMod p)) : GeneralFormalCircuit (ZMod p) Inputs unit where
  name := tableName
  main := main target
  Spec input _ _ := Valid input
  ProverAssumptions input _ _ := Valid input
  channelsWithRequirements := [stateChannel.toRaw]
  soundness := by
    circuit_proof_start [main, Gadgets.ToBits.rangeCheck, cursor, stateChannel, Valid]
    simpa only [sub_eq_zero] using h_holds
  completeness := by
    circuit_proof_start [main, Gadgets.ToBits.rangeCheck, cursor, stateChannel, Valid]
    simpa only [sub_eq_zero] using h_assumptions

/-- The one preallocated row is built immediately. Its private hint supplies two clock limbs.
Clean increments the outgoing multiplicity when the verifier demands the public endpoint. -/
def component (target : State (ZMod p)) : Component (ZMod p) where
  circuit := circuit target
  generation := .preallocated {
    channel := stateChannel
    trigger := .pull
    height := 1
    input _ := pure ⟨.fixed 1, .multiplicity, .witness (.hintGet tableName 2 0 0), .witness (.hintGet tableName 2 0 1)⟩
    rowOf _ := 0 }

theorem one_physical_row {target : State (ZMod p)} (table : Table (ZMod p))
    (installed : table.component = component target) : ∃ row, table.table = [row] := by
  have fixed := table.fixed_rows_match
  rw [installed] at fixed
  exact List.length_eq_one_iff.mp fixed.1

omit [Fact (2 ^ 25 < p)] in
private theorem range_empty (n : ℕ) (bound : 2 ^ n < p) (input : Expression (ZMod p)) (offset : ℕ) :
    (FlatOperation.interactions ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).ops.toFlat).filter
      (fun (i : AbstractInteraction (ZMod p)) => decide (i.channel = stateChannel.toRaw)) = [] :=
  InteractionRecovery.filter_interactions_formalAssertion_eq_nil
    (Gadgets.ToBits.rangeCheck n bound) stateChannel.toRaw input List.not_mem_nil List.not_mem_nil

theorem interactions (target : State (ZMod p)) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main target input).operations offset).interactionsWith stateChannel.toRaw =
      [(stateChannel.pulled (cursor (const target) input.high input.low)).toRaw,
       (stateChannel.pushedIf input.count (const target)).toRaw] := by
  simp only [main, circuit_norm, range_empty, List.nil_append]

theorem values (target : State (ZMod p)) (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p)) :
    ((main target input).operations offset).interactionValuesWith stateChannel.toRaw env =
      [stateChannel.pulledValue (cursor target (eval env input).high (eval env input).low),
       stateChannel.pushedIfValue (eval env input).count target] := by
  simp only [Operations.interactionValuesWith, interactions, List.map_cons, List.map_nil, Channel.eval_pulled,
    Channel.eval_pushedIf, ProvableType.eval_const]
  have eq : ProvableStruct.eval env (const target) = target := by
    rw [← ProvableStruct.eval_eq_eval, ProvableType.eval_const]
  simp only [cursor, circuit_norm, eq]

omit [Fact (2 ^ 25 < p)] in
/-- A checked pair of limbs reconstructs one 48-bit private clock. -/
theorem private_timestamp {publicClock head allocated : ℕ} (input : Inputs (ZMod p)) (valid : Valid input) :
    ∃ timestamp : BitVec 48, cursor (State.encode (p := p) publicClock head allocated) input.high input.low =
      State.encode timestamp.toNat head allocated := by
  have high := valid.2.2.1
  have low := valid.2.2.2
  let ticks := input.high.val * 2 ^ 24 + input.low.val
  have fits : ticks < 2 ^ 48 := by dsimp [ticks]; omega
  refine ⟨BitVec.ofNat 48 ticks, ?_⟩
  have div : ticks / 2 ^ 24 = input.high.val := by dsimp [ticks]; omega
  have mod : ticks % 2 ^ 24 = input.low.val := by dsimp [ticks]; omega
  simp only [State.encode, cursor, BitVec.toNat_ofNat, Nat.mod_eq_of_lt fits, div, mod, ZMod.natCast_zmod_val]

/-- The checked physical rows expose one private timestamp and exactly the two cursor occurrences. -/
theorem physical_projection (publicClock head allocated : ℕ) (table : Table (ZMod p))
    (installed : table.component = component (State.encode publicClock head allocated))
    (checked : table.Constraints) :
    ∃ timestamp : BitVec 48, table.interactionsWith stateChannel.toRaw =
      [stateChannel.pulledValue (State.encode timestamp.toNat head allocated),
       stateChannel.pushedValue (State.encode publicClock head allocated)] := by
  obtain ⟨row, rows⟩ := one_physical_row table installed
  have member : row ∈ table.table := by simp [rows]
  let env := table.environment row
  let input := valueFromOffset Inputs 0 env
  have constraints := checked row member
  rw [installed] at constraints
  let terminal := component (State.encode (p := p) publicClock head allocated)
  have valid : Valid input := by
    apply (Component.weakSoundness (component := terminal) (env := env) trivial constraints ?_).1
    rw [Operations.guarantees_iff _ _ _ (terminal.inChannelsOrGuarantees env)]
    intro channel member
    change channel ∈ [stateChannel.toRaw] at member
    obtain rfl := List.mem_singleton.mp member
    exact Operations.channelGuarantees_of_trivial _ (by simp [stateChannel, Channel.toRaw]) _ _
  obtain ⟨timestamp, cursorEq⟩ := private_timestamp (publicClock := publicClock) (head := head) (allocated := allocated) input valid
  refine ⟨timestamp, ?_⟩
  rw [Table.interactionsWith, rows, List.flatMap_cons, List.flatMap_nil, List.append_nil, installed,
    ← cursorEq]
  change ((component (State.encode publicClock head allocated)).operations.interactionsWith stateChannel.toRaw).map
    (AbstractInteraction.eval env) = _
  rw [Component.interactionsWith_eq]
  change ((main (State.encode publicClock head allocated) (varFromOffset Inputs 0)).operations (size Inputs)).interactionValuesWith stateChannel.toRaw env = _
  rw [values, eval_varFromOffset_valueFromOffset]
  change [_, stateChannel.pushedIfValue input.count _] = _
  rw [valid.2.1, valid.1]
  rfl

end SP1Clean.HostHintQueueTerminal
