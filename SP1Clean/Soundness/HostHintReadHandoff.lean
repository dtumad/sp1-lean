import SP1Clean.Soundness.HostCallOrder
import SP1Clean.Soundness.HostHintReadPartition

/-! # HINT_READ handler uniqueness from the instruction handoff

The actual handler consumes one full HostCall per physical row. Balanced handoff to these
handlers and the other handlers' unit pulls transfers instruction-clock uniqueness. The local
CPU theorem supplies producer uniqueness once the wrapper is projected onto its actual syscall
table. No caller supplies handler uniqueness or independently balanced per-call cursor tables.
-/

namespace SP1Clean.Soundness.HostHintReadHandoff

open Circuit Air.Flat HostHintReadCoverage

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def calls (table : Table (ZMod p)) : List (HostCallChip.Message (ZMod p)) :=
  (table.table.map table.environment).map fun env => (input env).call

omit [Fact (2 ^ 25 < p)] in
private theorem eval_call (row : Var HostHintReadChip.Inputs (ZMod p)) (env : Environment (ZMod p)) :
    eval env row.call = (eval env row).call := by
  cases row
  simp only [circuit_norm]

theorem handler_values (env : Environment (ZMod p)) :
    handler.operations.interactionValuesWith HostCallChip.channel.toRaw env =
      [HostCallChip.channel.pulledValue (input env).call] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0)).operations
    (size HostHintReadChip.Inputs)).interactionValuesWith HostCallChip.channel.toRaw env = _
  rw [HostHintReadChip.host_values, eval_call, eval_varFromOffset_valueFromOffset]
  rfl

theorem table_values (table : Table (ZMod p)) (component : table.component = handler) :
    table.interactionsWith HostCallChip.channel.toRaw = (calls table).map HostCallChip.channel.pulledValue := by
  simp only [Table.interactionsWith, calls, List.map_map, Function.comp_def, component]
  trans table.table.flatMap (fun physical => [HostCallChip.channel.pulledValue (input (table.environment physical)).call])
  · exact List.flatMap_congr (fun physical _ => handler_values (table.environment physical))
  · exact List.flatMap_pure_eq_map _ _

/-- Actual full-message handoff balance forbids duplicate HINT_READ handler clocks.
Other handlers must account for their own complete physical ledger as unit call pulls. -/
theorem handler_clocks_nodup (instructions handlers : Table (ZMod p))
    (producer : instructions.component = HostCallLedger.producer)
    (constraints : instructions.Constraints) (component : handlers.component = handler)
    (others : List (Table (ZMod p))) (otherCalls : List (HostCallChip.Message (ZMod p)))
    (otherLedger : others.flatMap (·.interactionsWith HostCallChip.channel.toRaw) =
      otherCalls.map HostCallChip.channel.pulledValue)
    (balanced : BalancedInteractions
      (instructions.interactionsWith HostCallChip.channel.toRaw ++
        handlers.interactionsWith HostCallChip.channel.toRaw ++
        others.flatMap (·.interactionsWith HostCallChip.channel.toRaw)))
    (unique : ((HostCallLedger.calls instructions).map HostCallLedger.clock).Nodup) :
    ((handlers.table.map handlers.environment).map HostHintReadPartition.callClock).Nodup := by
  rw [table_values handlers component, otherLedger, List.append_assoc, ← List.map_append] at balanced
  have allUnique := HostCallLedger.clocks_nodup instructions producer constraints
    (calls handlers ++ otherCalls) balanced unique
  rw [List.map_append] at allUnique
  simpa only [calls, List.map_map, Function.comp_def, HostCallLedger.clock,
    HostHintReadPartition.callClock, HostHintReadPartition.clock, HostHintReadChip.Inputs.first]
    using (List.nodup_append.mp allUnique).1

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Local AIR clock ordering and actual instruction handoff derive handler uniqueness.
The remaining projection premise is exact equality of physical active instruction inventories. -/
theorem handler_clocks_nodup_of_local {image : Model.Core.ProgramImage} {source : Model.Core.ExecutionSnapshot}
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (localConstraints : witness.Constraints) (localBalanced : witness.BalancedChannels)
    (instructions handlers : Table (ZMod p))
    (producer : instructions.component = HostCallLedger.producer)
    (constraints : instructions.Constraints) (component : handlers.component = handler)
    (projected : ((HostCallLedger.activeRows instructions).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (LocalCore.systemTable witness 3) syscallInstrsRow (·.is_real))
    (others : List (Table (ZMod p))) (otherCalls : List (HostCallChip.Message (ZMod p)))
    (otherLedger : others.flatMap (·.interactionsWith HostCallChip.channel.toRaw) =
      otherCalls.map HostCallChip.channel.pulledValue)
    (balanced : BalancedInteractions
      (instructions.interactionsWith HostCallChip.channel.toRaw ++
        handlers.interactionsWith HostCallChip.channel.toRaw ++
        others.flatMap (·.interactionsWith HostCallChip.channel.toRaw))) :
    ((handlers.table.map handlers.environment).map HostHintReadPartition.callClock).Nodup :=
  handler_clocks_nodup instructions handlers producer constraints component others otherCalls otherLedger balanced
    (LocalCore.hostCalls_clocks_nodup witness localConstraints localBalanced instructions projected)

/-- The local CPU and shared handoff/cursor ledgers supply the selected call's actual word-table
balance, without a separate handler-uniqueness or per-call-balance premise. -/
theorem balanced_for_of_local {image : Model.Core.ProgramImage} {source : Model.Core.ExecutionSnapshot}
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (localConstraints : witness.Constraints) (localBalanced : witness.BalancedChannels)
    (instructions handlers : Table (ZMod p))
    (producer : instructions.component = HostCallLedger.producer)
    (constraints : instructions.Constraints) (component : handlers.component = handler)
    (projected : ((HostCallLedger.activeRows instructions).map fun env => (HostCallLedger.input env).instruction) =
      activeSystemRows (LocalCore.systemTable witness 3) syscallInstrsRow (·.is_real))
    (others : List (Table (ZMod p))) (otherCalls : List (HostCallChip.Message (ZMod p)))
    (otherLedger : others.flatMap (·.interactionsWith HostCallChip.channel.toRaw) =
      otherCalls.map HostCallChip.channel.pulledValue)
    (handoff : BalancedInteractions
      (instructions.interactionsWith HostCallChip.channel.toRaw ++
        handlers.interactionsWith HostCallChip.channel.toRaw ++
        others.flatMap (·.interactionsWith HostCallChip.channel.toRaw)))
    (tables : List (Table (ZMod p)))
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (env : Environment (ZMod p)) (member : env ∈ handlers.table.map handlers.environment)
    (cursor : BalancedInteractions
      (handlers.interactionsWith HintReadWordChip.stateChannel.toRaw ++
        tables.flatMap (·.interactionsWith HintReadWordChip.stateChannel.toRaw))) :
    BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env) tables).flatMap
          (·.interactionsWith HintReadWordChip.stateChannel.toRaw)) :=
  HostHintReadPartition.balanced_for handlers component tables aligned env member
    (handler_clocks_nodup_of_local witness localConstraints localBalanced instructions handlers
      producer constraints component projected others otherCalls otherLedger handoff) cursor

end SP1Clean.Soundness.HostHintReadHandoff
