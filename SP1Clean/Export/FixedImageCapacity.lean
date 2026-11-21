import SP1Clean.Math.SP1Field
import SP1Clean.FormalModel.ShardResources
import SP1Clean.Proofs.Chips.FixedProgramProvider.Preprocessed
import SP1Clean.Native.Operations.WritePermission
import ToClean.Air.Footprint

/-! # Fixed Program and write-permission capacity

Every checked instruction contributes a distinct nonzero first byte to source RAM. A nonempty
writable gap ends at the start of a protected instruction or at the address-space limit. These
two facts pay for the verifier-fixed Program and permission providers using source payload alone.
-/

namespace SP1Clean.Export
open Air.Flat Semantics

open FixedProgramProvider.Preprocessed in
/-- Any physical table for the fixed Program provider spends exactly its immutable height
on the Program channel, including the rows whose lookup count is zero. -/
theorem fixedProgram_occurrences (image : ProgramImage)
    (table : Table (ZMod SP1Prime)) (installed : table.component = component image) :
    (table.interactionsWith Channels.programChannel.toRaw).length = height (p := SP1Prime) image := by
  have fixed := table.fixed_rows_match
  rw [installed] at fixed
  have physical : table.length = height (p := SP1Prime) image := fixed.1
  rw [Table.interactionsWith_length, physical, installed]
  have width : (component (p := SP1Prime) image).channelWidth Channels.programChannel.toRaw = 1 := by
    rw [Component.channelWidth, Component.interactionsWith_eq]
    change ((((circuit image).main (varFromOffset Input 0)).operations (size Input)).interactionsWith
      Channels.programChannel.toRaw).length = 1
    rw [main_program_interactions]
    rfl
  simp only [width, Nat.mul_one]

open WritePermissionProvider in
/-- The fixed writable-interval membership provider emits once per padded row. -/
theorem fixedPermission_occurrences (image : ProgramImage)
    (table : Table (ZMod SP1Prime)) (installed : table.component = membershipComponent image) :
    (table.interactionsWith image.writePermissionTable.channel.toRaw).length =
      (image.writePermissionTable (p := SP1Prime)).height := by
  have fixed := table.fixed_rows_match
  rw [installed] at fixed
  have physical : table.length = (image.writePermissionTable (p := SP1Prime)).height := fixed.1
  rw [Table.interactionsWith_length, physical, installed]
  simp [Component.channelWidth, Component.interactionsWith_eq, Component.rowOperations,
    membershipComponent, StaticTable.component, StaticTable.provider, circuit_norm]

end SP1Clean.Export

namespace SP1Clean.FormalModel.Shard
open Semantics Machine

/-- A global boundary-payload ceiling suffices to size both immutable image tables. The
remaining headroom applies separately to the Program and fixed permission membership channels.
The minimum nonempty Program block has 32 rows. -/
theorem AdmissibleExecution.fixed_image_capacity {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events) :
    let program := FixedProgramProvider.Preprocessed.height (p := SP1Prime) image
    let permission := (image.writePermissionTable (p := SP1Prime)).height
    let bound := 2 ^ Nat.clog 2 (max (limits.boundaryBytes - 124) 32)
    program ≤ bound ∧ permission ≤ bound ∧
      ∀ capacity other : ℕ, bound < capacity → other ≤ capacity - 1 - bound →
        program + other < capacity ∧ permission + other < capacity := by
  have valid := execution.1.1.1
  have rom := valid.rom_length_le_support
  have resources := execution.2.2.2.1
  rw [source.resources_realize] at resources
  have payload := resources .boundaryBytes
  change source.resources .boundaryBytes ≤ limits.boundaryBytes at payload
  have overhead : (source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card + 125 ≤
      source.resources .boundaryBytes := by
    simp only [ExecutionSnapshot.resources, HostState.payloadCost, hintPayloadCost, bytePayloadCost]
    omega
  change image.rom.length ≤ (source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card at rom
  have entries : image.rom.length + 1 ≤ limits.boundaryBytes - 124 := by omega
  let budget := max (limits.boundaryBytes - 124) 32
  have romBudget := entries.trans (Nat.le_max_left _ 32)
  have program : FixedProgramProvider.Preprocessed.height (p := SP1Prime) image ≤ 2 ^ Nat.clog 2 budget := by
    unfold FixedProgramProvider.Preprocessed.height
    split
    · exact Nat.one_le_pow _ _ (by decide)
    · rw [FixedProgramProvider.Preprocessed.rows_of_valid _ valid.1, image.programRows_length valid.2.1]
      exact Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.clog_mono_right 2
        (max_le (by omega) (Nat.le_max_right _ _)))
  have permission : (image.writePermissionTable (p := SP1Prime)).height ≤ 2 ^ Nat.clog 2 budget := by
    unfold StaticTable.height
    apply Nat.pow_le_pow_right (by decide : 0 < 2)
    apply Nat.clog_mono_right
    simpa only [ProgramImage.writePermissionTable, StaticTable.ofRows, List.length_map] using
      image.writableIntervals_length_le_rom.trans romBudget
  refine ⟨program, permission, ?_⟩
  intro capacity other small rest
  change 2 ^ Nat.clog 2 budget < capacity at small
  change other ≤ capacity - 1 - 2 ^ Nat.clog 2 budget at rest
  omega

/-- At the public ceiling that bounds each fixed RAM provider by 2^30 rows, the
Program and fixed permission tables each reserve at most 2^29 occurrences. -/
theorem AdmissibleExecution.fixed_image_headroom {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits SP1Prime image source target events)
    (ceiling : limits.boundaryBytes ≤ 2 ^ 29 + 124) :
    let program := FixedProgramProvider.Preprocessed.height (p := SP1Prime) image
    let permission := (image.writePermissionTable (p := SP1Prime)).height
    program ≤ 2 ^ 29 ∧ permission ≤ 2 ^ 29 ∧
      ∀ other ≤ SP1Prime - 1 - 2 ^ 29,
        program + other < SP1Prime ∧ permission + other < SP1Prime := by
  obtain ⟨program, permission, _⟩ := execution.fixed_image_capacity
  have budget : max (limits.boundaryBytes - 124) 32 ≤ 2 ^ 29 := max_le (by omega) (by decide)
  have physical := Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr budget)
  refine ⟨program.trans physical, permission.trans physical, ?_⟩
  intro other remaining
  exact ⟨(Nat.add_le_add (program.trans physical) remaining).trans_lt (by decide),
    (Nat.add_le_add (permission.trans physical) remaining).trans_lt (by decide)⟩

end SP1Clean.FormalModel.Shard
