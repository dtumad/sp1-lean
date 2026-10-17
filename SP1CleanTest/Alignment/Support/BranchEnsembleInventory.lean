import SP1CleanTest.Alignment.Support.BranchEnsembleChannels
import SP1CleanTest.Alignment.Support.BranchEnsembleLookups

/-! # Authenticated finite checking of the complete branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open Circuit Air.Flat SP1Clean.Model.Core

/-- The two remaining legacy fixed meanings retain their original identities. -/
theorem fixed_names (target : MemorySnapshot) : (fixed target).map (·.table.name) =
    ["sp1.native.hint_source_nodes",
      "sp1.native.hint_source_words"] := by
  simp only [List.map_cons, List.map_nil, fixed, FiniteLookup.ofStatic,
    HintQueue.sourceTable, HintQueue.sourceWordTable, StaticTable.ofRows,
    StaticTable.toTable, Table.toRaw]

/-- The checker authenticates all physical lookups and the separate verifier's complete channels. -/
def description (target : MemorySnapshot) : EnsembleCheck ((assembly target).withChannels (channels target)) where
  lookups := fixed target
  lookups_unique := by rw [fixed_names]; decide
  lookups_complete := lookups_complete target
  channels_unique := channels_unique target
  channels_complete := channels_complete target
  verifier_channels_complete := verifier_channels_complete target

/-- Check actual physical rows and all original channels after equivalent registry reindexing. -/
def checkPhysical (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) : Bool :=
  (description target).checkWitness SP1Prime ((witness target input seeds bounded).withChannels (channels target))

/-- The Boolean checker proves the raw predicates on the original full host assembly. -/
theorem checkPhysical_iff (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    checkPhysical target input seeds bounded = true ↔
      (witness target input seeds bounded).Constraints ∧ (witness target input seeds bounded).BalancedChannels := by
  rw [checkPhysical, EnsembleCheck.checkWitness_iff]
  exact and_congr (EnsembleWitness.withChannels_constraints _ _)
    (EnsembleWitness.withChannels_balanced _ _ (channels_membership target))

/-- Reject malformed seeds before construction, then check the original complete physical witness. -/
def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) : Bool :=
  match seeds? target input consumers with
  | none => false
  | some seeds => if bounded : seeds.length ≤ UInt64.size then
      checkPhysical target input seeds bounded else false

end SP1Clean.Audit.BranchEnsemble
