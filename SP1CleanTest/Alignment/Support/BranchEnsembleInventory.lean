import SP1CleanTest.Alignment.Support.BranchEnsembleFixture
import SP1CleanTest.Alignment.Support.InstalledAssemblyInventory

/-! # Authenticated finite checking of the complete branch host assembly -/

namespace SP1Clean.Audit.BranchEnsemble

open SP1CleanTest.Alignment.InstalledAssembly
open Circuit Air.Flat SP1Clean.Model.Core

/-- Check actual physical rows and every registered channel, including their capacity bound. -/
def checkPhysical (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) : Bool :=
  (description (context target)).checkWitness (witness target input seeds bounded)

/-- The Boolean checker proves the raw predicates on the original full host assembly. -/
theorem checkPhysical_iff (target : MemorySnapshot) (input : SP1PublicIO Fp) (seeds : List Seed)
    (bounded : seeds.length ≤ UInt64.size) :
    checkPhysical target input seeds bounded = true ↔
      (assembly (context target)).interactionsFit .logUp (witness target input seeds bounded).heights ∧
      (witness target input seeds bounded).Constraints ∧ (witness target input seeds bounded).Balanced .logUp :=
  EnsembleCheck.checkWitness_iff _ _

/-- Reject malformed seeds before construction, then check the original complete physical witness. -/
def check (target : MemorySnapshot) (input : SP1PublicIO Fp) (consumers : List Seed) : Bool :=
  match seeds? target input consumers with
  | none => false
  | some seeds => if bounded : seeds.length ≤ UInt64.size then
      checkPhysical target input seeds bounded else false

end SP1Clean.Audit.BranchEnsemble
