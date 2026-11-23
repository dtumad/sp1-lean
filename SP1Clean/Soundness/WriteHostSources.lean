import SP1Clean.Proofs.Chips.SyscallInstrsChip.Ledger
import SP1Clean.Soundness.HostCallProjection
import SP1Clean.Soundness.HintReadWriteLedger
import SP1Clean.Native.Operations.WriteProbeAccess
import ToClean.Air.Authentication
import ToClean.Air.ComponentReplacement

/-! # WRITE predecessor versions from ECALL and both HINT_READ word transfers

The ECALL sites are the three original register pulls. Both HINT_READ word components
publish the old aligned RAM word. The upper clock comes from the call or word transfer itself.
-/

namespace SP1Clean.WriteProbe.HostSources

open Circuit Air.Flat Soundness Channels AccessSupply

/-- All non-refresh host producers of predecessor versions. -/
inductive Family where
  | ecall
  | word (last : Bool)
deriving DecidableEq

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- Current installed producer of the original Memory transitions. -/
def original : Family → Component (ZMod p)
  | .ecall => HostCallLedger.producer
  | .word last => HintReadCoverage.component last

/-- Each key is the typed Memory message emitted by the actual registered access. -/
def sites : (family : Family) → List (Receipt.Projection (ZMod p) (original (p := p) family).Input MemoryMsg)
  | .ecall =>
    [⟨fun r _ => r.is_real, fun r _ => SyscallInstrsChip.memPullMsg r r.op_a_memory r.op_a⟩,
     ⟨fun r _ => r.is_real, fun r _ => SyscallInstrsChip.memPullMsg r r.op_b_memory r.op_b⟩,
     ⟨fun r _ => r.is_real, fun r _ => SyscallInstrsChip.memPullMsg r r.op_c_memory r.op_c⟩]
  | .word _ => [⟨fun r _ => r.2, fun r _ => r.1.ram.prior⟩]

/-- Incoming released bus time as the original high/low pair; HINT_READ words retain their call clock. -/
def clock : (family : Family) → Var (original (p := p) family).Input (ZMod p) →
    Expression (ZMod p) × Expression (ZMod p)
  | .ecall, r => ((HostCallChip.message r).clk_high, (HostCallChip.message r).clk_low)
  | .word _, r => (r.1.ram.clk_high, r.1.ram.clockLow)

private def project (family : Family) (site : Receipt.Projection (ZMod p) (original (p := p) family).Input MemoryMsg) :
    Receipt.Projection (ZMod p) (original (p := p) family).Input Readback :=
  ⟨site.gate, fun input offset => atClock (clock family input) (site.message input offset)⟩

/-- Original component and generation mode with only the additional private publications. -/
def component (family : Family) : Component (ZMod p) where
  circuit := Receipt.many (original family).circuit readbackChannel (fun _ _ => trivial) ((sites family).map (project family))
  generation := (original family).generation
  Assumptions := (original family).Assumptions
  circuit_assumptions_of_assumptions := by
    intro i input data fixed declared holds
    have unchanged := Receipt.many_assumptions (original (p := p) family).circuit
      readbackChannel (fun _ _ => trivial) ((sites family).map (project family))
    have name := Receipt.many_name (original (p := p) family).circuit
      readbackChannel (fun _ _ => trivial) ((sites family).map (project family))
    exact (congrFun (congrFun unchanged input) data).mpr
      ((original family).circuit_assumptions_of_assumptions i input data fixed (name ▸ declared) holds)

private theorem fresh (family : Family) : readbackChannel.toRaw ∉ (original (p := p) family).circuit.channels := by
  intro used
  have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
  cases family with
  | ecall => change false = true at present; contradiction
  | word last => cases last <;> change false = true at present <;> contradiction

/-- One private source occurrence per original pull, retaining its exact activity gate and old word. -/
theorem row_receipts (family : Family) (env : Environment (ZMod p)) :
    let input := varFromOffset (original (p := p) family).Input 0
    let offset := size (original (p := p) family).Input
    (component family).operations.interactionValuesWith readbackChannel.toRaw env =
      (sites family).map (fun site => readbackChannel.pushedIfValue (env (site.gate input offset))
        (eval env (atClock (clock family input) (site.message input offset)))) := by
  let input := varFromOffset (F := ZMod p) (original (p := p) family).Input 0
  let offset := size (original (p := p) family).Input
  have added := Receipt.many_receipts (original (p := p) family).circuit readbackChannel (fun _ _ => trivial)
    ((sites family).map (project family)) input offset
  rw [InteractionRecovery.interactionsWith_main_eq_nil (original family).circuit.base _ input offset (fresh family), List.nil_append] at added
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
  change ((((component family).circuit.main input).operations offset).interactionsWith readbackChannel.toRaw).map (AbstractInteraction.eval env) = _
  rw [show (((component family).circuit.main input).operations offset).interactionsWith readbackChannel.toRaw = _ from added]
  simp only [List.map_map, Function.comp_def, project, Channel.eval_pushedIf, ProvableType.eval_field, input, offset]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_pulled (env : Environment (ZMod p)) (gate : Expression (ZMod p)) (msg : Var MemoryMsg (ZMod p)) :
    memoryChannel.pulledIfValue (env gate) (eval env msg) =
      ((⟨.pull, gate, msg⟩ : ChannelInteraction (memoryChannel (p := p))).toRaw.eval env) := by
  exact ((Channel.eval_pulledIf (channel := memoryChannel) (enabled := gate) (msg := msg) (env := env)).trans
    (congrArg (fun weight => memoryChannel.pulledIfValue weight (eval env msg)) (ProvableType.eval_field env gate))).symm

private theorem actual_pull (family : Family) (env : Environment (ZMod p))
    (site : Receipt.Projection (ZMod p) (original (p := p) family).Input MemoryMsg) (member : site ∈ sites family) :
    let input := varFromOffset (original (p := p) family).Input 0
    let offset := size (original (p := p) family).Input
    memoryChannel.pulledIfValue (env (site.gate input offset)) (eval env (site.message input offset)) ∈
      (original family).operations.interactionValuesWith memoryChannel.toRaw env := by
  cases family with
  | ecall =>
    rw [show (original (p := p) .ecall).operations.interactionValuesWith memoryChannel.toRaw env = _ from HostCallProjection.memory_values env]
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change _ ∈ ((((SyscallInstrsChip.main (p := p) (varFromOffset SyscallInstrsChip.Inputs 0)).operations (size SyscallInstrsChip.Inputs)).interactionsWith memoryChannel.toRaw).map (AbstractInteraction.eval env))
    rw [SyscallInstrsChip.Ledger.syscallInstrsInteractionsWith_memory]
    simp only [sites, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp only [List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false] <;>
      first
      | left; exact eval_pulled env _ _
      | right; right; left; exact eval_pulled env _ _
      | right; right; right; right; left; exact eval_pulled env _ _
  | word last =>
    simp only [sites, List.mem_singleton] at member
    subst site
    simp only [Operations.interactionValuesWith, Component.interactionsWith_eq, Component.rowOperations]
    change _ ∈ (((HintReadWordChip.circuit (p := p) last).main (varFromOffset HintReadWordChip.RowInput 0)).operations (size HintReadWordChip.RowInput)).interactionValuesWith memoryChannel.toRaw env
    rw [HintReadWordChip.guarded_memory_values]
    exact List.mem_cons_self ..

/-- Install the new sources on an existing table without changing its rows or original generation. -/
def publish (family : Family) (table : Table (ZMod p)) (registered : table.component = original family) :
    Table (ZMod p) :=
  table.withComponent (component family) (by rw [registered]; exact Receipt.many_width _ _ (fun _ _ => trivial) _) (by
      rw [registered]
      funext rows
      dsimp only [component, Component.FixedRowsMatch]
      split <;> rfl)
    (by rw [registered]; exact Receipt.many_name _ _ (fun _ _ => trivial) _)
    (by rw [registered]; rfl)

theorem publish_constraints (family : Family) (table : Table (ZMod p)) (registered : table.component = original family) :
    (publish family table registered).Constraints ↔ table.Constraints := by
  apply Table.withComponent_constraints
  · rw [registered]
    exact Receipt.many_constraints _ _ (fun _ _ => trivial) _
  · rw [registered]
    exact Receipt.many_lookups _ _ (fun _ _ => trivial) _

theorem publish_interactions (family : Family) (table : Table (ZMod p))
    (registered : table.component = original family) (channel : RawChannel (ZMod p)) (other : channel ≠ readbackChannel.toRaw) :
    (publish family table registered).interactionsWith channel = table.interactionsWith channel := by
  apply Table.withComponent_interactions
  rw [registered]
  exact Receipt.many_interactions _ _ (fun _ _ => trivial) _ channel other

/-- A host source's upper bound is the original physical call clock at the row. -/
def upper (family : Family) (env : Environment (ZMod p)) : ZMod p × ZMod p :=
  let time := clock (p := p) family (varFromOffset _ 0)
  (env time.1, env time.2)

/-- Every positive receipt comes from a positive predecessor on the original host Memory channel in
the same physical row, with the exact call clock. Both last-word and continuation variants are covered. -/
theorem publish_authenticates (family : Family) (table : Table (ZMod p)) (registered : table.component = original family) :
    (publish family table registered).Authenticates readbackChannel (FromPredecessor table (upper family)) := by
  intro physical member interaction live active
  let env := table.environment physical
  change interaction ∈ (component family).operations.interactionValuesWith readbackChannel.toRaw env at live
  rw [row_receipts] at live
  obtain ⟨site, seen, rfl⟩ := List.mem_map.mp live
  let input := varFromOffset (F := ZMod p) (original (p := p) family).Input 0
  let offset := size (original (p := p) family).Input
  refine ⟨_, rfl, physical, member, env (site.gate input offset), eval env (site.message input offset),
    active.1, ?_, ?_⟩
  · rw [registered]
    exact actual_pull family env site seen
  · exact eval_atClock env _ _

/-- ECALL contributes three private occurrences per physical row. Each HINT_READ word contributes one. -/
theorem publication_count (family : Family) (table : Table (ZMod p)) (registered : table.component = original family) :
    ((publish family table registered).interactionsWith readbackChannel.toRaw).length =
      table.length * (match family with | .ecall => 3 | .word _ => 1) := by
  simp only [publish, Table.interactionsWith, Table.withComponent, Table.environment, row_receipts, Table.length]
  induction table.table with
  | nil => simp
  | cons row rows ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, Nat.succ_mul] at ih ⊢
    rw [ih, Nat.add_comm]
    cases family <;> rfl

end SP1Clean.WriteProbe.HostSources
