import SP1Clean.FormalModel.Contracts.SnapshotMemory
import SP1Clean.Model.Core.RegisterSnapshotTable
import SP1Clean.Model.Channels
import ToClean.Circuit.InteractionRecovery
import Clean.Utils.Tactics

/-! # Register source records for an arbitrary local snapshot

Each row authenticates its index and complete value against the fixed snapshot table, then emits
one zero-time Memory record. A witness cannot choose the incoming register value. No activity
selector is needed: absent provider rows are represented by an empty table.
-/

namespace SP1Clean.SnapshotRegisterProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

abbrev Inputs := RegisterSnapshotRow

def message {R : Type} [Zero R] (input : Inputs R) : MemoryMsg R :=
  ⟨0, 0, input.index, 0, 0, input.value⟩

/-- A fixed-table row has its exact snapshot value at a canonical register location. -/
theorem snapshotSpec (snapshot : MemorySnapshot) (input : Inputs (ZMod p))
    (member : snapshot.registerTable.Spec input) :
    MemoryBoundary.SnapshotAtSpec snapshot input.index.val (message input) := by
  obtain ⟨bound, valueBound, valueEq⟩ := snapshot.registerTable_sound input member
  have decoded : MemoryMsg.locOf (message input) = MemLoc.reg (BitVec.ofNat 5 input.index.val) := by
    simp only [MemoryMsg.locOf, message, bound, and_self, if_true]
  refine ⟨⟨valueBound, by simp [MemoryMsg.ClkBound, message],
    by simp [MemoryMsg.timeNat, clkNat, message], ?_, ?_, ?_⟩,
    by simp [MemoryBoundary.address, message, Word.toNat]⟩
  · rw [decoded]; trivial
  · exact (congrArg snapshot.read decoded).trans valueEq.symm
  · refine ⟨?_, ?_⟩
    · apply Word.isU64_of_cases
      · simpa only [MemoryBoundary.address, message, circuit_norm] using
          lt_trans bound (by norm_num : 32 < 2 ^ 16)
      all_goals norm_num [MemoryBoundary.address, message]
    · rw [decoded]
      simp only [MemoryBoundary.address, message, Word.toNat, circuit_norm,
        ZMod.val_zero, zero_mul, add_zero, MemLoc.busAddress,
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt bound]

def main (snapshot : MemorySnapshot) (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  lookup snapshot.registerTable.toTable input
  let record := message input
  memoryChannel.push record
  return record

instance elaborated (snapshot : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs MemoryMsg (main snapshot) := by elaborate_circuit

omit [Fact (2 ^ 17 < p)] in
theorem main_memory_interactions (snapshot : MemorySnapshot) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main snapshot input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pushed (message input)).toRaw] := by
  simp only [main, circuit_norm]

def circuit (snapshot : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs MemoryMsg where
  main := main snapshot
  elaborated := elaborated snapshot
  Spec input output _ := MemoryBoundary.SnapshotAtSpec snapshot input.index.val output
  ProverAssumptions input _ _ := snapshot.registerTable.Spec input
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [message]
    have valid := snapshotSpec snapshot ⟨input_index, input_value⟩ h_holds
    exact ⟨valid, fun _ _ => ⟨valid.1.1, valid.1.2.1⟩⟩
  completeness := by
    circuit_proof_start [message]
    exact h_assumptions

/-- Every semantic register index has a proof-independent row constructor. -/
abbrev populate := @MemorySnapshot.registerRow

theorem populate_assumptions (snapshot : MemorySnapshot) (index : BitVec 5)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit snapshot).ProverAssumptions (populate snapshot index) data hint :=
  (snapshot.registerTable_spec _).mpr ⟨index, rfl⟩

end SP1Clean.SnapshotRegisterProvider
