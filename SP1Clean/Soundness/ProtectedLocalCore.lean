import SP1Clean.Soundness.LocalCoreEnsemble
import SP1Clean.Proofs.Chips.ProtectedStore
import SP1Clean.Native.Operations.WritePermission

/-! # Local AIR with explicit ROM write protection

Four instruction components acquire byte-permission requests, and one fixed-interval provider
supplies them. The complete source verifier and all other tables are retained. This is the native
assembly intended for the capstone; transport of the existing local grounding theorem to its
additional ledger is a separate proof obligation, not an assumed execution guarantee.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The four store positions in the shared instruction inventory, after the seven boundary rows. -/
def tables (image : ProgramImage) (source : ExecutionSnapshot) : List (Component (ZMod p)) :=
  let stores := LocalCore.tables image source
    |>.set 25 ⟨ProtectedStore.byte⟩
    |>.set 26 ⟨ProtectedStore.half⟩
    |>.set 27 ⟨ProtectedStore.word⟩
    |>.set 28 ⟨ProtectedStore.double⟩
  stores ++ [⟨WritePermissionProvider.circuit image⟩]

def ensemble (image : ProgramImage) (source : ExecutionSnapshot) : Ensemble (ZMod p) SP1PublicIO where
  tables := tables image source
  channels := WritePermissionProvider.channel.toRaw :: (LocalCore.ensemble image source).channels
  verifier := LocalCore.verifier image source
  verifier_length_zero := by intros; rfl

theorem tables_length (image : ProgramImage) (source : ExecutionSnapshot) :
    (tables (p := p) image source).length = 60 := by
  simp only [tables, List.length_append, List.length_set, List.length_singleton, LocalCore.tables_length]

end SP1Clean.Soundness.ProtectedLocalCore
