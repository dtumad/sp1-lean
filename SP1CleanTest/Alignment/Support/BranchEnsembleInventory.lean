module

public import SP1CleanTest.Alignment.Support.BranchEnsembleFixture
public import SP1CleanTest.Alignment.Support.InstalledAssemblyInventory

/-! # Authenticated finite checking of the complete branch host assembly -/

@[expose] public section

namespace SP1Clean.Audit.BranchEnsemble

open SP1CleanTest.Alignment.InstalledAssembly
open Circuit Air.Flat SP1Clean.Model.Core

/-- Check actual physical rows and all original channels after equivalent registry reindexing. -/
def checkPhysical (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) : Bool :=
  (description (context target)).checkWitness SP1Prime ((witness target input seeds bounded).withChannels (channels (context target)))

/-- The Boolean checker proves the raw predicates on the original full host assembly. -/
theorem checkPhysical_iff (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    checkPhysical target input seeds bounded = true ↔
      (witness target input seeds bounded).Constraints ∧ (witness target input seeds bounded).BalancedChannels := by
  rw [checkPhysical, EnsembleCheck.checkWitness_iff]
  exact and_congr (EnsembleWitness.withChannels_constraints _ _)
    (EnsembleWitness.withChannels_balanced _ _ (channels_membership (context target)))

/-- Reject malformed seeds before construction, then check the original complete physical witness. -/
def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) : Bool :=
  match seeds? target input consumers with
  | none => false
  | some seeds => if bounded : seeds.length ≤ UInt64.size then
      checkPhysical target input seeds bounded else false

end SP1Clean.Audit.BranchEnsemble
