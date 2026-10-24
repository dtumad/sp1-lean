module

public import ToClean.Circuit.Guarded
public import ToClean.Circuit.SubcircuitProjection
public import ToClean.Air.StaticProvider
public import SP1Clean.FormalModel.Contracts.SnapshotMemory
public import SP1Clean.Model.Core.RegisterSnapshotTable
public import SP1Clean.Model.Channels
public import ToClean.Circuit.InteractionRecovery
public import Clean.Utils.Tactics

/-! # Register source records for an arbitrary local snapshot

Each sparse row requests its index and complete value from the snapshot's fixed-column
membership provider, then emits one zero-time Memory record. The private membership channel
authenticates the incoming value. No activity selector is needed: absent Memory-provider rows
are represented by an empty table; the separate fixed provider retains all 32 register rows.
-/

@[expose] public section

namespace SP1Clean.SnapshotRegisterProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
theorem membership_height_lt_uint64 (snapshot : MemorySnapshot) :
    (snapshot.registerTable (p := p)).height < UInt64.size := by
  have padded := (snapshot.registerTable (p := p)).height_lt_double
  rw [snapshot.registerTable_length] at padded
  norm_num [UInt64.size] at *
  omega

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
  snapshot.registerTable.channel.pull ⟨input, 1⟩
  let record := message input
  memoryChannel.push record
  return record

instance elaborated (snapshot : MemorySnapshot) :
    ElaboratedCircuit (ZMod p) Inputs MemoryMsg (main snapshot) where
  localLength _ := 0
  output input _ := message input
  channelsWithGuarantees := [snapshot.registerTable.channel.toRaw]

omit [Fact (2 ^ 17 < p)] in
theorem main_memory_interactions (snapshot : MemorySnapshot) (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main snapshot input).operations offset).interactionsWith memoryChannel.toRaw =
      [(memoryChannel.pushed (message input)).toRaw] := by
  simp [main, circuit_norm, StaticTable.channel, MemorySnapshot.registerTable,
    StaticTable.ofRows, memoryChannel]

def circuit (snapshot : MemorySnapshot) : GeneralFormalCircuit (ZMod p) Inputs MemoryMsg where
  name := "sp1.native.memory.snapshot.registers"
  main := main snapshot
  elaborated := elaborated snapshot
  Spec input output _ := MemoryBoundary.SnapshotAtSpec snapshot input.index.val output
  ProverAssumptions input _ _ := snapshot.registerTable.Spec input
  channelsWithRequirements := [memoryChannel.toRaw]
  soundness := by
    circuit_proof_start [message, StaticTable.channel]
    have valid := snapshotSpec snapshot ⟨input_index, input_value⟩ h_holds
    exact ⟨valid, fun _ _ => ⟨valid.1.1, valid.1.2.1⟩⟩
  completeness := by
    circuit_proof_start [message, StaticTable.channel]
    exact h_assumptions

/-- Every semantic register index has a proof-independent row constructor. -/
abbrev populate := @MemorySnapshot.registerRow

theorem populate_assumptions (snapshot : MemorySnapshot) (index : BitVec 5)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (circuit snapshot).ProverAssumptions (populate snapshot index) data hint :=
  (snapshot.registerTable_spec _).mpr ⟨index, rfl⟩

omit [Fact (2 ^ 17 < p)] in
/-- Register authentication uses the private membership channel, with no legacy lookup. -/
@[circuit_norm] theorem main_lookupNames (snapshot : MemorySnapshot)
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main snapshot input).operations offset).lookups.map (·.table.name) = [] := by
  simp [main, circuit_norm]

/-- Every physical interaction supports Boolean row activity without a legacy lookup. -/
instance guardSupported (snapshot : MemorySnapshot) : Guarded.Supported (circuit snapshot (p := p)) :=
  Guarded.Supported.of_emitted_requirements _
    (fun input offset => List.map_eq_nil_iff.mp (main_lookupNames snapshot input offset))
    (by
      intro selected member
      change selected ∈ [snapshot.registerTable.channel.toRaw, memoryChannel.toRaw] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> infer_instance)
    (by
      intro input offset selected member _ interaction occurs
      have same : selected = memoryChannel.toRaw := by
        simpa only [circuit, List.mem_singleton] using member
      subst selected
      change interaction ∈ ((main snapshot input).operations offset).interactionsWith
        memoryChannel.toRaw at occurs
      rw [main_memory_interactions] at occurs
      have same := List.mem_singleton.mp occurs
      subst interaction
      rfl)

end SP1Clean.SnapshotRegisterProvider
