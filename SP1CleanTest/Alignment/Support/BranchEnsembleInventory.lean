import SP1CleanTest.Alignment.Support.BranchEnsembleChannels
import SP1CleanTest.Alignment.Support.BranchEnsembleLookups

/-! # A faithful finite export descriptor for the branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core

/-- Physical positions have unique stable export names; instruction identity stays in the circuits. -/
def componentNames : List String := (List.range 89).map fun index => "table-" ++ toString index

/-- All ten fixed tables keep their original names, with explicit target-snapshot namespaces. -/
theorem fixed_names (target : MemorySnapshot) : (fixed target).map (·.table.name) =
    ["sp1.native.source_registers", "sp1.native.initial_memory", "sp1.native.program", "ByteXor",
      "sp1.native.syscall_code", "sp1.native.write_permission", "sp1.native.hint_source_nodes",
      "sp1.native.hint_source_words", "sp1.native.target_registers", "sp1.native.target_memory"] := by
  simp only [List.map_cons, List.map_nil, fixed, FiniteLookup.ofStatic, MemorySnapshot.registerTable, ByteMemory.fixedTable,
    ProgramImage.programTable, SyscallKind.fixedTable, ProgramImage.writePermissionTable,
    HintQueue.sourceTable, HintQueue.sourceWordTable, xorFixed, StaticTable.ofRows,
    StaticTable.toTable, Table.fromStatic, Table.toRaw, Gadgets.Xor.ByteXorTable]

/-- The export description authenticates every original lookup predicate and channel identity. -/
def description (target : MemorySnapshot) : EnsembleExport ((assembly target).withChannels channels) where
  componentNames := componentNames
  names_length := rfl
  verifierName := "public-verifier"
  names_unique := by decide
  names_nonempty := by decide
  channels_unique := by
    change (channels.map RawChannel.name).Nodup
    decide
  channels_nonempty := by
    intro channel member
    have names : ∀ name ∈ channels.map RawChannel.name, name ≠ "" := by decide
    exact names _ (List.mem_map_of_mem (f := RawChannel.name) member)
  lookups := fixed target
  lookups_unique := by rw [fixed_names]; decide
  lookups_nonempty := by
    intro table member
    have present := List.mem_map_of_mem (f := fun table : FiniteLookup Fp => table.table.name) member
    rw [fixed_names] at present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> decide
  lookups_complete := lookups_complete target
  channels_complete := channels_complete target

/-- Check actual physical rows and all original channels after equivalent registry reindexing. -/
def checkPhysical (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed) : Bool :=
  (description target).checkWitness SP1Prime ((witness target input seeds).withChannels channels)

/-- The Boolean checker proves the raw predicates on the original full host assembly. -/
theorem checkPhysical_iff (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed) :
    checkPhysical target input seeds = true ↔
      (witness target input seeds).Constraints ∧ (witness target input seeds).BalancedChannels := by
  rw [checkPhysical, EnsembleExport.checkWitness_iff]
  exact and_congr (EnsembleWitness.withChannels_constraints _ _)
    (EnsembleWitness.withChannels_balanced _ _ (channels_membership target))

/-- Reject malformed seeds before construction, then check the original complete physical witness. -/
def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) : Bool :=
  match seeds? target input consumers with
  | none => false
  | some seeds => checkPhysical target input seeds

end SP1Clean.Audit.BranchEnsemble
