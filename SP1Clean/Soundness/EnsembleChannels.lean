import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.TableBuild

/-!
# Every table speaks only on the ensemble's channels

Clean's `Ensemble` carries a `channels` list but does not *constrain* its components to it — nothing
in the structure says a table cannot emit on a channel the ensemble never declared. For `sp1Ensemble`
that constraint holds, and this file proves it.

The fact is load-bearing for any argument that reads the whole ledger at once and then asks which
bus a given key came from. `Interaction.toAccess` puts the emitting channel's own `name` in the key,
so a key already determines a channel *name*; turning that into a channel needs to know the name
ranges over a finite set with no collisions, which is exactly what this file plus
`Model/Channels.lean`'s per-pair distinctness supplies.

Each chip reduces the same way: `circuit.channels` is `channelsWithGuarantees ++
channelsWithRequirements`, the guarantee half goes through the chip's own `elaborated` instance
(which is where the six chips with a *derived* elaborated — Jal, Jalr, Branch, UType, LoadX0,
StoreByte — get theirs computed rather than declared), and the requirement half is a literal field.
Both are definitional, so the whole sweep is `rfl` plus `circuit_norm`.
-/

namespace SP1Clean.Soundness

open SP1Clean
open Air.Flat
open Circuit
open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel exitChannel
  syscallChannel publicValuesChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- **The five buses the current tables actually speak on.** The ensemble declares two more —
`syscallChannel` and `publicValuesChannel`, the `SyscallInstrs` row's buses — but until that table
joins (S4b) no registered table touches them, and this list is what makes that a *uniform* theorem:
every per-table subset fact below lands here, so silence on any channel outside this list follows
for all tables at once (`sp1AllTables_channel_not_mem_of_not_core`) instead of costing a per-table
sweep per new channel, the way the Exit wave did. -/
def sp1CoreChannels : List (RawChannel (ZMod p)) :=
  [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
   Channels.programChannel.toRaw, Channels.memoryChannel.toRaw,
   Channels.exitChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma sp1CoreChannels_eq :
    sp1CoreChannels (p := p) =
      [Channels.stateChannel.toRaw, Channels.byteChannel.toRaw,
       Channels.programChannel.toRaw, Channels.memoryChannel.toRaw,
       Channels.exitChannel.toRaw] := rfl

/-! ## The 25 instruction chips -/

private theorem addChip_channels_subset :
    (AddChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddChip.circuit (p := p)).channelsWithGuarantees =
      (AddChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem addiChip_channels_subset :
    (AddiChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddiChip.circuit (p := p)).channelsWithGuarantees =
      (AddiChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddiChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem addwChip_channels_subset :
    (AddwChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddwChip.circuit (p := p)).channelsWithGuarantees =
      (AddwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem subChip_channels_subset :
    (SubChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubChip.circuit (p := p)).channelsWithGuarantees =
      (SubChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem subwChip_channels_subset :
    (SubwChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubwChip.circuit (p := p)).channelsWithGuarantees =
      (SubwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem bitwiseChip_channels_subset :
    (BitwiseChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BitwiseChip.circuit (p := p)).channelsWithGuarantees =
      (BitwiseChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BitwiseChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem ltChip_channels_subset :
    (LtChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LtChip.circuit (p := p)).channelsWithGuarantees =
      (LtChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LtChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem shiftLeftChip_channels_subset :
    (ShiftLeftChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftLeftChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftLeftChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftLeftChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem shiftRightChip_channels_subset :
    (ShiftRightChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftRightChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftRightChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftRightChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem jalChip_channels_subset :
    (JalChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalChip.circuit (p := p)).channelsWithGuarantees =
      (JalChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem jalrChip_channels_subset :
    (JalrChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalrChip.circuit (p := p)).channelsWithGuarantees =
      (JalrChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalrChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem branchChip_channels_subset :
    (BranchChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BranchChip.circuit (p := p)).channelsWithGuarantees =
      (BranchChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BranchChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem uTypeChip_channels_subset :
    (UTypeChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (UTypeChip.circuit (p := p)).channelsWithGuarantees =
      (UTypeChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (UTypeChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadByteChip_channels_subset :
    (LoadByteChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadByteChip.circuit (p := p)).channelsWithGuarantees =
      (LoadByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadHalfChip_channels_subset :
    (LoadHalfChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadHalfChip.circuit (p := p)).channelsWithGuarantees =
      (LoadHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadWordChip_channels_subset :
    (LoadWordChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadWordChip.circuit (p := p)).channelsWithGuarantees =
      (LoadWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadDoubleChip_channels_subset :
    (LoadDoubleChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (LoadDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem loadX0Chip_channels_subset :
    (LoadX0Chip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadX0Chip.circuit (p := p)).channelsWithGuarantees =
      (LoadX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeByteChip_channels_subset :
    (StoreByteChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreByteChip.circuit (p := p)).channelsWithGuarantees =
      (StoreByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeHalfChip_channels_subset :
    (StoreHalfChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreHalfChip.circuit (p := p)).channelsWithGuarantees =
      (StoreHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeWordChip_channels_subset :
    (StoreWordChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreWordChip.circuit (p := p)).channelsWithGuarantees =
      (StoreWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem storeDoubleChip_channels_subset :
    (StoreDoubleChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (StoreDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem mulChip_channels_subset :
    (MulChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MulChip.circuit (p := p)).channelsWithGuarantees =
      (MulChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (MulChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem divRemChip_channels_subset :
    (DivRemChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (DivRemChip.circuit (p := p)).channelsWithGuarantees =
      (DivRemChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (DivRemChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem aluX0Chip_channels_subset :
    (AluX0Chip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AluX0Chip.circuit (p := p)).channelsWithGuarantees =
      (AluX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AluX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **Every instruction chip stays on the ensemble's four buses.** -/
theorem sp1Tables_channels_subset : ∀ c ∈ sp1Tables (p := p),
    c.circuit.channels ⊆ sp1CoreChannels (p := p) := by
  intro c hc
  fin_cases hc
  exacts [addChip_channels_subset, addiChip_channels_subset, addwChip_channels_subset, subChip_channels_subset, subwChip_channels_subset, bitwiseChip_channels_subset, ltChip_channels_subset, shiftLeftChip_channels_subset, shiftRightChip_channels_subset, jalChip_channels_subset, jalrChip_channels_subset, branchChip_channels_subset, uTypeChip_channels_subset, loadByteChip_channels_subset, loadHalfChip_channels_subset, loadWordChip_channels_subset, loadDoubleChip_channels_subset, loadX0Chip_channels_subset, storeByteChip_channels_subset, storeHalfChip_channels_subset, storeWordChip_channels_subset, storeDoubleChip_channels_subset, mulChip_channels_subset, divRemChip_channels_subset, aluX0Chip_channels_subset]

/-! ## The 28 boundary/provider tables, and the verifier row -/

private theorem u8RangeProvider_channels_subset :
    (ByteChip.U8Range.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem msbProvider_channels_subset :
    (ByteChip.MSB.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.MSB.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.MSB.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem andProvider_channels_subset :
    (ByteChip.AndByte.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem orProvider_channels_subset :
    (ByteChip.OrByte.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem xorProvider_channels_subset :
    (ByteChip.XorByte.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem ltuProvider_channels_subset :
    (ByteChip.Ltu.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem programProvider_channels_subset :
    (ProgramProviderChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ProgramProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ProgramProviderChip.circuit (p := p)).channelsWithRequirements = [programChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem memoryInitProvider_channels_subset :
    (MemoryProviderChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (MemoryProviderChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

set_option linter.unusedSectionVars false in
private theorem memoryFinalizeProvider_channels_subset :
    (MemoryFinalizeChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithGuarantees = [memoryChannel.toRaw] from rfl,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem memoryBumpProvider_channels_subset :
    (MemoryBumpChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, memoryChannel.toRaw] from rfl,
    show (MemoryBumpChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem stateBumpProvider_channels_subset :
    (StateBumpChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StateBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, stateChannel.toRaw] from rfl,
    show (StateBumpChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem rangeProvider_channels_subset (width : RangeChip.Width) :
    (RangeChip.circuitFor (p := p) width).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (RangeChip.circuitFor (p := p) width).channelsWithGuarantees = [] from rfl,
    show (RangeChip.circuitFor (p := p) width).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false, false_or] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem haltProvider_channels_subset :
    (HaltChip.circuit (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (HaltChip.circuit (p := p)).channelsWithGuarantees
      = [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
         exitChannel.toRaw] from rfl,
    show (HaltChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

private theorem verifier_channels_subset :
    (sp1StateVerifier (p := p)).channels ⊆ sp1CoreChannels (p := p) := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (sp1StateVerifier (p := p)).channelsWithGuarantees
      = [stateChannel.toRaw, byteChannel.toRaw, exitChannel.toRaw] from rfl,
    show (sp1StateVerifier (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [List.not_mem_nil, List.mem_cons, or_false] at h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- The `SyscallInstrs` table is the one provider that leaves the core five. It stays inside the
ensemble's declared seven, which is the property the ledger actually needs. -/
theorem syscallInstrsProvider_channels_subset :
    (SyscallInstrsChip.circuit (p := p)).channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SyscallInstrsChip.circuit (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, stateChannel.toRaw, programChannel.toRaw, memoryChannel.toRaw,
       exitChannel.toRaw, syscallChannel.toRaw, publicValuesChannel.toRaw] from rfl,
    show (SyscallInstrsChip.circuit (p := p)).channelsWithRequirements =
      [memoryChannel.toRaw] from rfl] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **Every boundary/provider table stays on the core five, except the `SyscallInstrs` table.** -/
theorem sp1ProviderTables_channels_subset_core : ∀ c ∈ sp1ProviderTables (p := p),
    c.circuit.channels ⊆ sp1CoreChannels (p := p) ∨
      c = (⟨SyscallInstrsChip.circuit⟩ : Component (ZMod p)) := by
  intro c hc
  rw [sp1ProviderTables_explicit, List.mem_append, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Or.inl u8RangeProvider_channels_subset, Or.inl msbProvider_channels_subset,
      Or.inl andProvider_channels_subset, Or.inl orProvider_channels_subset,
      Or.inl xorProvider_channels_subset, Or.inl ltuProvider_channels_subset]
  · rw [sp1RangeProviderTables] at hc
    obtain ⟨width, -, rfl⟩ := List.mem_map.mp hc
    exact Or.inl (rangeProvider_channels_subset width)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    exacts [Or.inl programProvider_channels_subset, Or.inl memoryInitProvider_channels_subset,
      Or.inl memoryFinalizeProvider_channels_subset, Or.inl memoryBumpProvider_channels_subset,
      Or.inl stateBumpProvider_channels_subset, Or.inl haltProvider_channels_subset, Or.inr rfl]

/-- The `SyscallInstrs` table's stable ensemble position. Spelled here as well as in `BumpDecode`
(whose `syscallInstrsIndex` is definitionally this same number) because this file sits *below* that
one and cannot cite it. -/
def syscallTablePosition : ℕ := instructionTableCount + stateSilentProviderTableCount + 2

/-- The syscall table is the twenty-ninth provider, and every other provider id is something else.
Stated over `Fin` rather than a bounded `ℕ` so `decide` sees a *closed* proposition: an `ℕ`-indexed
`getElem` carries its bounds proof as a term, and after `interval_cases` that proof is a local
hypothesis, which `decide` refuses to look at. -/
theorem providerTableId_all_ne_syscall :
    ∀ j : Fin ProviderTableId.all.length, j.val ≠ 29 →
      ProviderTableId.all[j] ≠ .syscallInstrs := by decide

/-- **Every provider but the syscall table stays on the five core buses.** The disjunctive form
`sp1ProviderTables_channels_subset_core` is what a *membership* argument can offer; this is the same
content keyed on the id, which is what a *positional* argument needs. -/
theorem providerTableFor_channels_subset_core_of_ne (id : ProviderTableId)
    (hne : id ≠ .syscallInstrs) :
    (providerTableFor (p := p) id).circuit.channels ⊆ sp1CoreChannels (p := p) := by
  cases id with
  | byte provider =>
      cases provider
      exacts [u8RangeProvider_channels_subset, msbProvider_channels_subset,
        andProvider_channels_subset, orProvider_channels_subset,
        xorProvider_channels_subset, ltuProvider_channels_subset]
  | range width => exact rangeProvider_channels_subset width
  | program => exact programProvider_channels_subset
  | memoryInit => exact memoryInitProvider_channels_subset
  | memoryFinalize => exact memoryFinalizeProvider_channels_subset
  | memoryBump => exact memoryBumpProvider_channels_subset
  | stateBump => exact stateBumpProvider_channels_subset
  | halt => exact haltProvider_channels_subset
  | syscallInstrs => exact absurd rfl hne

/-- **Positional core-only classification.** Every ensemble position except the syscall table's is
core-only. This is the form that lets a witness-level argument reach the *table* rather than only its
component: the index is what identifies the physical row list, and `Component` equality cannot be
refuted (the components differ in their `Input` type map, and type-level injectivity is not
available). -/
theorem sp1Ensemble_tables_channels_subset_core_of_ne (i : ℕ)
    (hi : i < (sp1Ensemble (p := p)).tables.length) (hne : i ≠ syscallTablePosition) :
    ((sp1Ensemble (p := p)).tables[i]'hi).circuit.channels ⊆ sp1CoreChannels (p := p) := by
  have hlen : (sp1Ensemble (p := p)).tables.length = 55 := by
    simp [sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]
  rw [hlen] at hi
  have hpos : syscallTablePosition = 54 := by
    simp [syscallTablePosition, instructionTableCount, stateSilentProviderTableCount]
  rw [hpos] at hne
  by_cases hlt : i < 25
  · have hget : ((sp1Ensemble (p := p)).tables[i]'(by rw [hlen]; omega))
        = (sp1Tables (p := p))[i]'(by rw [sp1Tables_length]; exact hlt) := by
      change ((sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i]'_) = _
      rw [List.getElem_append_left]
    rw [hget]
    exact sp1Tables_channels_subset _ (List.getElem_mem _)
  · have hall : ProviderTableId.all.length = 30 := by decide
    have hj : i - 25 < ProviderTableId.all.length := by omega
    have hget : ((sp1Ensemble (p := p)).tables[i]'(by rw [hlen]; omega))
        = providerTableFor (p := p) (ProviderTableId.all[i - 25]'hj) := by
      change ((sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i]'_) = _
      rw [List.getElem_append_right (by rw [sp1Tables_length]; omega)]
      simp only [sp1Tables_length, sp1ProviderTables, List.getElem_map]
    -- Rewrite the *channel list*, not the component: `Component` is dependent, so `rw` on it
    -- generates an ill-typed motive, while `c.circuit.channels` has a non-dependent codomain.
    have hch := congrArg (fun c : Component (ZMod p) => c.circuit.channels) hget
    rw [hch]
    have hne29 : i - 25 ≠ 29 := by omega
    exact providerTableFor_channels_subset_core_of_ne (p := p) _
      (providerTableId_all_ne_syscall ⟨i - 25, hj⟩ hne29)

/-- **Every registered table stays on the five core buses, with exactly one exception.**

The `SyscallInstrs` table is that exception, and naming it here is the honest form: it is the only
table that speaks on the syscall and public-values buses, so a blanket "everything is core-only"
claim would now be false. Stating the carve-out as a disjunction rather than deleting the theorem
keeps the *other* fifty-four tables' silence a one-line consequence, which is what the two buses'
balance still rests on while the syscall table's trace is empty. -/
theorem sp1AllTables_channels_subset_core :
    ∀ component ∈ (sp1Ensemble (p := p)).allTables,
      component.circuit.channels ⊆ sp1CoreChannels (p := p) ∨
        component = (⟨SyscallInstrsChip.circuit⟩ : Component (ZMod p)) := by
  intro component hc
  rw [Ensemble.allTables, List.mem_cons, sp1Ensemble_tables, List.mem_append] at hc
  rcases hc with rfl | hc | hc
  · exact Or.inl verifier_channels_subset
  · exact Or.inl (sp1Tables_channels_subset _ hc)
  · exact sp1ProviderTables_channels_subset_core _ hc

/-- The core buses are among the declared channels. -/
theorem sp1CoreChannels_subset :
    sp1CoreChannels (p := p) ⊆ (sp1Ensemble (p := p)).channels := by
  intro ch h
  simp only [sp1CoreChannels_eq, List.mem_cons, List.not_mem_nil, or_false] at h
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- **The ensemble's tables speak only on the ensemble's channels** — verifier row included.

Clean's `Ensemble` does not impose this, so it is a fact about `sp1Ensemble` specifically. -/
theorem sp1Ensemble_allTables_channels_subset :
    ∀ component ∈ (sp1Ensemble (p := p)).allTables,
      component.circuit.channels ⊆ (sp1Ensemble (p := p)).channels := by
  intro component hc
  rcases sp1AllTables_channels_subset_core component hc with hcore | rfl
  · exact List.Subset.trans hcore sp1CoreChannels_subset
  · exact syscallInstrsProvider_channels_subset

/-- Membership of a witness table's component in the ensemble's component list. -/
theorem witness_table_component_mem (witness : EnsembleWitness (sp1Ensemble (p := p)))
    {table : Air.Flat.Table (ZMod p)} (htable : table ∈ witness.allTables) :
    table.component ∈ (sp1Ensemble (p := p)).allTables := by
  rw [Air.Flat.EnsembleWitness.allTables, List.mem_cons] at htable
  rw [Air.Flat.Ensemble.allTables, List.mem_cons]
  rcases htable with rfl | htable
  · exact Or.inl rfl
  · refine Or.inr ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
    have hlen : i < (sp1Ensemble (p := p)).tables.length := by
      rw [witness.same_length]; exact hi
    rw [← witness.same_circuits i hlen]
    exact List.getElem_mem hlen

/-- **A witness is silent on a non-core channel exactly when its syscall table has no rows.**

Two reasons compose, one per table: fifty-four of the fifty-five tables never name the channel, and
the fifty-fifth names it but has nothing to say. The hypothesis is what the deterministic compiler
supplies by construction — `syscallInstrsTraceInputs` is the empty list — and it is precisely the
thing that stops being true when the compiler learns to emit syscall rows, which is the point at
which these buses need a real balance argument instead of silence. -/
theorem witness_interactionsWith_eq_nil_of_not_core
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hEmpty : ∀ t, witness.tables[syscallTablePosition]? = some t → t.table = [])
    {ch : RawChannel (ZMod p)} (hch : ch ∉ sp1CoreChannels (p := p)) :
    witness.interactionsWith ch = [] := by
  rw [Air.Flat.EnsembleWitness.interactionsWith, List.flatMap_eq_nil_iff]
  intro table htable
  rw [Air.Flat.EnsembleWitness.allTables, List.mem_cons] at htable
  rcases htable with rfl | htable
  · refine Air.Flat.Table.interactionsWith_nil_of_channel_not_mem fun hmem => hch ?_
    rw [Air.Flat.EnsembleWitness.verifierTable_component] at hmem
    exact verifier_channels_subset hmem
  · obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp htable
    have hlen : i < (sp1Ensemble (p := p)).tables.length := by rw [witness.same_length]; exact hi
    by_cases hidx : i = syscallTablePosition
    · subst hidx
      rw [Air.Flat.Table.interactionsWith_eq_filter, Air.Flat.Table.interactions,
        hEmpty _ (List.getElem?_eq_getElem hi)]
      rfl
    · refine Air.Flat.Table.interactionsWith_nil_of_channel_not_mem fun hmem => hch ?_
      have hchan := congrArg (fun c : Component (ZMod p) => c.circuit.channels)
        (witness.same_circuits i hlen)
      exact sp1Ensemble_tables_channels_subset_core_of_ne i hlen hidx (hchan ▸ hmem)

/-- SP1's syscall bus carries nothing while the syscall table has no rows. -/
theorem witness_syscallChannel_silent (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hEmpty : ∀ t, witness.tables[syscallTablePosition]? = some t → t.table = []) :
    witness.interactionsWith Channels.syscallChannel.toRaw = [] :=
  witness_interactionsWith_eq_nil_of_not_core witness hEmpty (by
    simp [sp1CoreChannels_eq, Channels.syscallChannel_eq_stateChannel_false,
      Channels.syscallChannel_eq_byteChannel_false,
      Channels.syscallChannel_eq_programChannel_false,
      Channels.syscallChannel_eq_memoryChannel_false,
      Channels.syscallChannel_eq_exitChannel_false])

/-- The native public-values bus carries nothing while the syscall table has no rows. -/
theorem witness_publicValuesChannel_silent (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (hEmpty : ∀ t, witness.tables[syscallTablePosition]? = some t → t.table = []) :
    witness.interactionsWith Channels.publicValuesChannel.toRaw = [] :=
  witness_interactionsWith_eq_nil_of_not_core witness hEmpty (by
    simp [sp1CoreChannels_eq, Channels.publicValuesChannel_eq_stateChannel_false,
      Channels.publicValuesChannel_eq_byteChannel_false,
      Channels.publicValuesChannel_eq_programChannel_false,
      Channels.publicValuesChannel_eq_memoryChannel_false,
      Channels.publicValuesChannel_eq_exitChannel_false])

omit [Fact (2 ^ 24 < p)] in
/-- The empty interaction list balances: nothing was sent and nothing was received. -/
theorem balancedInteractions_nil :
    BalancedInteractions ([] : List (Interaction (ZMod p))) := by
  constructor
  · left
    rw [List.length_nil, ZMod.ringChar_zmod_n]
    exact (Fact.out (p := p.Prime)).pos
  · intro msg
    rfl

/-- **The seven buses have seven distinct names**, so a channel name identifies its channel.

This is what turns `Interaction.toAccess`'s key — which carries the emitting channel's `name` — into
a statement about *which* channel produced an access. -/
theorem channel_eq_of_name_eq {c₁ c₂ : RawChannel (ZMod p)}
    (h₁ : c₁ ∈ (sp1Ensemble (p := p)).channels) (h₂ : c₂ ∈ (sp1Ensemble (p := p)).channels)
    (hname : c₁.name = c₂.name) : c₁ = c₂ := by
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso
         revert hname
         simp only [Channel.toRaw_name, stateChannel, byteChannel, programChannel, memoryChannel,
           exitChannel, Channels.syscallChannel, Channels.publicValuesChannel]
         decide)


/-- **The seven buses have seven distinct kinds too**, so an access's `InteractionKind` identifies
its channel just as its name does. This is the form the ledger's kind-filter needs — and it is the
proof a new ensemble channel *owes*: a channel classified `.Unmodelled` by `kindOf` would collide
with nothing today, but the moment a second one joined, this theorem is where the build fails
instead of State balance silently absorbing the pair. -/
theorem channel_eq_of_kindOf_eq {c₁ c₂ : RawChannel (ZMod p)}
    (h₁ : c₁ ∈ (sp1Ensemble (p := p)).channels) (h₂ : c₂ ∈ (sp1Ensemble (p := p)).channels)
    (hkind : kindOf c₁.name = kindOf c₂.name) : c₁ = c₂ := by
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at h₁ h₂
  rcases h₁ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases h₂ with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso
         revert hkind
         simp [Channel.toRaw_name, stateChannel, byteChannel, programChannel, memoryChannel,
           exitChannel, Channels.syscallChannel, Channels.publicValuesChannel, kindOf])

/-- **The side condition `Model/CleanLedger.lean`'s kind-filter asks of a table**, discharged for
every table of this ensemble: an interaction whose kind matches a declared channel's *is* on that
channel. Both halves are already proved — the table emits only on the ensemble's channels, and those
five have five distinct kinds. -/
theorem interactions_channel_eq_of_kindOf (table : Table (ZMod p))
    (hcomponent : table.component ∈ (sp1Ensemble (p := p)).allTables)
    (channel : RawChannel (ZMod p)) (hchannel : channel ∈ (sp1Ensemble (p := p)).channels) :
    ∀ i ∈ table.interactions, kindOf i.channel.name = kindOf channel.name →
      i.channel = channel := by
  intro i hi hkind
  exact channel_eq_of_kindOf_eq
    (sp1Ensemble_allTables_channels_subset _ hcomponent
      (Air.Flat.Table.channel_mem_channels_of_mem_interactions table i hi))
    hchannel hkind

/-! ## Exit-channel silence of the non-halt tables

The Exit bus connects exactly two parties: the Halt table's gated hand-off pushes and the
state-boundary verifier's ungated `⟨exit_code⟩` pull.  These lemmas record the silent side,
component by component, reusing each subset lemma's channel-list incantation; the exit-channel
accounting layer (`Soundness/ExitAccounting.lean`) consumes them through the positional table
decompositions. -/

private theorem addChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddChip.circuit (p := p)).channelsWithGuarantees =
      (AddChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem addiChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddiChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddiChip.circuit (p := p)).channelsWithGuarantees =
      (AddiChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddiChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem addwChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AddwChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AddwChip.circuit (p := p)).channelsWithGuarantees =
      (AddwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AddwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem subChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (SubChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubChip.circuit (p := p)).channelsWithGuarantees =
      (SubChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem subwChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (SubwChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (SubwChip.circuit (p := p)).channelsWithGuarantees =
      (SubwChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (SubwChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem bitwiseChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (BitwiseChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BitwiseChip.circuit (p := p)).channelsWithGuarantees =
      (BitwiseChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BitwiseChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem ltChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LtChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LtChip.circuit (p := p)).channelsWithGuarantees =
      (LtChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LtChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem shiftLeftChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ShiftLeftChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftLeftChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftLeftChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftLeftChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem shiftRightChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ShiftRightChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ShiftRightChip.circuit (p := p)).channelsWithGuarantees =
      (ShiftRightChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (ShiftRightChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem jalChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (JalChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalChip.circuit (p := p)).channelsWithGuarantees =
      (JalChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem jalrChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (JalrChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (JalrChip.circuit (p := p)).channelsWithGuarantees =
      (JalrChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (JalrChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem branchChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (BranchChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (BranchChip.circuit (p := p)).channelsWithGuarantees =
      (BranchChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (BranchChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem uTypeChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (UTypeChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (UTypeChip.circuit (p := p)).channelsWithGuarantees =
      (UTypeChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (UTypeChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadByteChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadByteChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadByteChip.circuit (p := p)).channelsWithGuarantees =
      (LoadByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadHalfChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadHalfChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadHalfChip.circuit (p := p)).channelsWithGuarantees =
      (LoadHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadWordChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadWordChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadWordChip.circuit (p := p)).channelsWithGuarantees =
      (LoadWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadDoubleChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadDoubleChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (LoadDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem loadX0Chip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (LoadX0Chip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (LoadX0Chip.circuit (p := p)).channelsWithGuarantees =
      (LoadX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (LoadX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeByteChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreByteChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreByteChip.circuit (p := p)).channelsWithGuarantees =
      (StoreByteChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreByteChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeHalfChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreHalfChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreHalfChip.circuit (p := p)).channelsWithGuarantees =
      (StoreHalfChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreHalfChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeWordChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreWordChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreWordChip.circuit (p := p)).channelsWithGuarantees =
      (StoreWordChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreWordChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem storeDoubleChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StoreDoubleChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StoreDoubleChip.circuit (p := p)).channelsWithGuarantees =
      (StoreDoubleChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (StoreDoubleChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem mulChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MulChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MulChip.circuit (p := p)).channelsWithGuarantees =
      (MulChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (MulChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem divRemChip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (DivRemChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (DivRemChip.circuit (p := p)).channelsWithGuarantees =
      (DivRemChip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (DivRemChip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem aluX0Chip_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (AluX0Chip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (AluX0Chip.circuit (p := p)).channelsWithGuarantees =
      (AluX0Chip.elaborated (p := p)).channelsWithGuarantees from rfl,
    show (AluX0Chip.circuit (p := p)).channelsWithRequirements = [stateChannel.toRaw, memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem u8RangeProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.U8Range.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.U8Range.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem msbProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.MSB.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.MSB.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.MSB.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem andProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.AndByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.AndByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem orProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.OrByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.OrByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem xorProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.XorByte.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.XorByte.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem ltuProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ByteChip.Ltu.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ByteChip.Ltu.circuit (p := p)).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem programProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (ProgramProviderChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (ProgramProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (ProgramProviderChip.circuit (p := p)).channelsWithRequirements = [programChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem memoryInitProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryProviderChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryProviderChip.circuit (p := p)).channelsWithGuarantees = [] from rfl,
    show (MemoryProviderChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

set_option linter.unusedSectionVars false in
private theorem memoryFinalizeProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryFinalizeChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithGuarantees = [memoryChannel.toRaw] from rfl,
    show (MemoryFinalizeChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem memoryBumpProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (MemoryBumpChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (MemoryBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, memoryChannel.toRaw] from rfl,
    show (MemoryBumpChip.circuit (p := p)).channelsWithRequirements = [memoryChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem stateBumpProvider_exitChannel_not_mem :
    (exitChannel (p := p)).toRaw ∉ (StateBumpChip.circuit (p := p)).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (StateBumpChip.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw, stateChannel.toRaw] from rfl,
    show (StateBumpChip.circuit (p := p)).channelsWithRequirements = [] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

private theorem rangeProvider_exitChannel_not_mem (width : RangeChip.Width) :
    (exitChannel (p := p)).toRaw ∉ (RangeChip.circuitFor (p := p) width).channels := by
  intro h
  rw [GeneralFormalCircuit.channels, List.mem_append,
    show (RangeChip.circuitFor (p := p) width).channelsWithGuarantees = [] from rfl,
    show (RangeChip.circuitFor (p := p) width).channelsWithRequirements = [byteChannel.toRaw] from rfl] at h
  simp only [circuit_norm, List.mem_cons, List.not_mem_nil, or_self,
    Nat.reduceEqDiff, false_and, and_false] at h

/-- **No instruction chip speaks on the Exit bus.** -/
theorem sp1Tables_exitChannel_not_mem : ∀ c ∈ sp1Tables (p := p),
    (exitChannel (p := p)).toRaw ∉ c.circuit.channels := by
  intro c hc
  fin_cases hc
  exacts [addChip_exitChannel_not_mem, addiChip_exitChannel_not_mem, addwChip_exitChannel_not_mem, subChip_exitChannel_not_mem, subwChip_exitChannel_not_mem, bitwiseChip_exitChannel_not_mem, ltChip_exitChannel_not_mem, shiftLeftChip_exitChannel_not_mem, shiftRightChip_exitChannel_not_mem, jalChip_exitChannel_not_mem, jalrChip_exitChannel_not_mem, branchChip_exitChannel_not_mem, uTypeChip_exitChannel_not_mem, loadByteChip_exitChannel_not_mem, loadHalfChip_exitChannel_not_mem, loadWordChip_exitChannel_not_mem, loadDoubleChip_exitChannel_not_mem, loadX0Chip_exitChannel_not_mem, storeByteChip_exitChannel_not_mem, storeHalfChip_exitChannel_not_mem, storeWordChip_exitChannel_not_mem, storeDoubleChip_exitChannel_not_mem, mulChip_exitChannel_not_mem, divRemChip_exitChannel_not_mem, aluX0Chip_exitChannel_not_mem]

/-- **The only provider components that name the Exit bus are the Halt table and the
`SyscallInstrs` table.** The syscall table's Exit push is gated by `is_halt`, so unlike the Halt
table it cannot be excluded by its channel list; while its trace is empty its Exit contribution is
nil for the other reason, and once it carries rows the exit accounting owes it a real block. -/
theorem sp1ProviderTables_exitChannel_not_mem (k : ℕ)
    (bound : k < (sp1ProviderTables (p := p)).length) (notHalt : k ≠ 28)
    (notSyscall : k ≠ 29) :
    (exitChannel (p := p)).toRaw ∉ ((sp1ProviderTables (p := p))[k]).circuit.channels := by
  rw [sp1ProviderTables_length] at bound
  interval_cases k
  · exact u8RangeProvider_exitChannel_not_mem
  · exact msbProvider_exitChannel_not_mem
  · exact andProvider_exitChannel_not_mem
  · exact orProvider_exitChannel_not_mem
  · exact xorProvider_exitChannel_not_mem
  · exact ltuProvider_exitChannel_not_mem
  all_goals first
  | exact (notHalt rfl).elim
  | exact (notSyscall rfl).elim
  | exact rangeProvider_exitChannel_not_mem _
  | exact programProvider_exitChannel_not_mem
  | exact memoryInitProvider_exitChannel_not_mem
  | exact memoryFinalizeProvider_exitChannel_not_mem
  | exact memoryBumpProvider_exitChannel_not_mem
  | exact stateBumpProvider_exitChannel_not_mem

end SP1Clean.Soundness
