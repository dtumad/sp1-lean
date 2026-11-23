import SP1Clean.Proofs.Chips.HostCallChip.Ledger
import SP1Clean.Proofs.Chips.CoreSyscallChip.Bridge
import ToClean.Air.UnitBalance
import ToClean.Air.TableBuild

/-! # Exact instruction-to-handler inventory

The physical wrapper emits one complete message per active instruction. Binary activity is
derived from its raw constraints; padding contributes zero. A balanced handoff to unit handler
pulls therefore identifies their complete messages with the actual active instruction inventory.
`HostLocalHandoff` instantiates this algebra over the installed ensemble and its physical receiver registry.
-/

namespace SP1Clean.Soundness.HostCallLedger

open Circuit Air.Flat HostCallChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- Match the field equality used by Clean's gated balance filters. -/
local instance cleanBalanceDecidableEq : DecidableEq (ZMod p) := FiniteField.instDecidableEq

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def producer : Component (ZMod p) := { circuit := HostCallChip.circuit, Assumptions := (HostCallChip.circuit).Assumptions, generation := HostCallChip.generation }

def input (env : Environment (ZMod p)) : SyscallInstrsChip.Inputs (ZMod p) :=
  valueFromOffset SyscallInstrsChip.Inputs 0 env

def call (env : Environment (ZMod p)) : Message (ZMod p) :=
  message (input env)

def clock (message : Message (ZMod p)) : ZMod p × ZMod p := (message.clk_high, message.clk_low)

def activeRows (table : Table (ZMod p)) (data : ProverData (ZMod p)) : List (Environment (ZMod p)) :=
  (table.table.map (Environment.fromArray · data)).filter fun env => decide ((input env).is_real = 1)

omit [Fact (2 ^ 25 < p)] in
/-- Membership exposes semantic activity without leaking the filter's field-equality instance. -/
theorem activeRows_is_real (table : Table (ZMod p)) (data : ProverData (ZMod p))
    (env : Environment (ZMod p)) (member : env ∈ activeRows table data) :
    (input env).is_real = 1 :=
  of_decide_eq_true (List.mem_filter.mp member).2

def calls (table : Table (ZMod p)) (data : ProverData (ZMod p)) : List (Message (ZMod p)) := (activeRows table data).map call

private theorem main_binary (row : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) (constraints : ((HostCallChip.main row).operations offset).ConstraintsHold env) :
    (eval env row).is_real = 0 ∨ (eval env row).is_real = 1 := by
  have core := HostCallChip.instruction_of_constraints row offset env constraints
  have profile := CoreSyscallChip.profile_of_constraints row offset env core
  exact profile.1

omit [Fact (2 ^ 25 < p)] in
private theorem eval_memory (memory : Circuits.Types.RegisterAccessCols (Expression (ZMod p)))
    (env : Environment (ZMod p)) :
    (ProvableStruct.eval env memory).prev_value = Eval.eval env memory.prev_value := by
  cases memory
  simp only [circuit_norm]

private theorem main_values (row : Var SyscallInstrsChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p)) :
    ((HostCallChip.main row).operations offset).interactionValuesWith channel.toRaw env =
      [channel.pushedIfValue (eval env row).is_real (message (eval env row))] := by
  simp only [Operations.interactionValuesWith, HostCallChip.main_host_interactions,
    List.map_cons, List.map_nil, Channel.eval_pushedIf]
  cases row
  simp only [message, circuit_norm, eval_memory]

/-- The full-code guard enforces binary activity before any semantic Memory grounding. -/
theorem binary_of_constraints (env : Environment (ZMod p))
    (constraints : producer.operations.ConstraintsHold env) :
    (input env).is_real = 0 ∨ (input env).is_real = 1 := by
  have binary := main_binary (varFromOffset SyscallInstrsChip.Inputs 0) (size SyscallInstrsChip.Inputs) env
    ((Component.constraintsHold_iff env).mp constraints)
  simpa only [eval_varFromOffset_valueFromOffset, input] using binary

/-- The actual evaluated row emits exactly its binary-gated full call. -/
theorem row_values (env : Environment (ZMod p)) :
    producer.operations.interactionValuesWith channel.toRaw env =
      [channel.pushedIfValue (input env).is_real (call env)] := by
  have projected := main_values (varFromOffset SyscallInstrsChip.Inputs 0) (size SyscallInstrsChip.Inputs) env
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HostCallChip.main (varFromOffset SyscallInstrsChip.Inputs 0)).operations
    (size SyscallInstrsChip.Inputs)).interactionValuesWith channel.toRaw env = _
  simpa only [eval_varFromOffset_valueFromOffset, input, call] using projected

/-- Every physical row remains in the ledger, including zero-multiplicity padding. -/
theorem table_values (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = producer)
    : table.interactionsWith channel.toRaw =
      (table.table.map (Environment.fromArray · data)).map fun env =>
        channel.pushedIfValue (input env).is_real (call env) := by
  simp only [Table.interactionsWith, List.map_map, Function.comp_def]
  rw [component]
  trans table.table.flatMap (fun physical =>
    [channel.pushedIfValue (input (Environment.fromArray physical data)).is_real
      (call (Environment.fromArray physical data))])
  · apply List.flatMap_congr
    intro physical _
    exact row_values _
  · exact List.flatMap_pure_eq_map _ _

/-- Complete handler messages are a permutation of actual active instruction calls.
The characteristic bound comes from the original balanced physical ledger. -/
theorem calls_perm (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = producer)
    (constraints : table.Constraints) (consumed : List (Message (ZMod p)))
    (balanced : BalancedInteractions
      ((table.interactionsWith channel.toRaw).filter (fun interaction => decide (interaction.mult ≠ 0)) ++
        consumed.map channel.pulledValue)) :
    (calls table data).Perm consumed := by
  rw [table_values table data component] at balanced
  have binary : ∀ env ∈ table.table.map (Environment.fromArray · data),
      (input env).is_real = 0 ∨ (input env).is_real = 1 := by
    intro env member
    obtain ⟨physical, present, rfl⟩ := List.mem_map.mp member
    have checked := binary_of_constraints _ (component ▸ constraints physical present)
    have cells : input (table.environment physical) = input (Environment.fromArray physical data) :=
      ProvableType.valueFromOffset_congr _ _ (fun _ _ => rfl)
    simpa only [cells] using checked
  rw [channel.pushedIfValues_filter_nonzero _ _ _ binary] at balanced
  apply (channel.balanced_unit_iff (calls table data) consumed).mp _
  simpa only [calls, activeRows, List.map_map, Function.comp_def] using balanced

/-- A handler cannot duplicate an event clock when its complete calls balance unique producers. -/
theorem clocks_nodup (table : Table (ZMod p)) (data : ProverData (ZMod p)) (component : table.component = producer)
    (constraints : table.Constraints) (consumed : List (Message (ZMod p)))
    (balanced : BalancedInteractions
      ((table.interactionsWith channel.toRaw).filter (fun interaction => decide (interaction.mult ≠ 0)) ++
        consumed.map channel.pulledValue))
    (unique : ((calls table data).map clock).Nodup) :
    (consumed.map clock).Nodup :=
  ((calls_perm table data component constraints consumed balanced).map clock).nodup_iff.mp unique

end SP1Clean.Soundness.HostCallLedger
