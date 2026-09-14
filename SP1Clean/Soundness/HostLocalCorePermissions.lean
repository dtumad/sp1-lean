import SP1Clean.Soundness.HostLocalCore
import SP1Clean.Soundness.ProtectedLocalCorePermissions

/-! # Byte permission authentication with host effects installed

The host wrapper is silent on WritePermission. The retained protected store/provider inventory
therefore remains exhaustive when appended components prove that they emit only unit pulls or
padding on this channel. The extended ensemble's own balance authenticates every requested byte;
no projection of its Memory or permission balance is used.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The fixed image provider is still the only possible positive permission contributor. -/
theorem component_permission_source (image : ProgramImage) (source : ExecutionSnapshot)
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p)))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (component : Component (ZMod p)) (member : component ∈ (ensemble image source auxiliary channels).allTables) :
    component = (⟨WritePermissionProvider.circuit image⟩ : Component (ZMod p)) ∨ WritePermission.Pulls component := by
  simp only [Ensemble.allTables, ensemble, List.mem_cons] at member
  rcases member with verifier | member
  · apply ProtectedLocalCore.component_permission_source image source component
    exact List.mem_cons.mpr (Or.inl verifier)
  · rcases List.mem_append.mp member with core | extra
    · rcases List.mem_or_eq_of_mem_set core with original | rfl
      · exact ProtectedLocalCore.component_permission_source image source component (List.mem_cons_of_mem _ original)
      · right
        apply WritePermission.pulls_of_silent
        intro used
        have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
        change false = true at present
        contradiction
    · exact Or.inr (pulls component extra)

/-- Every active request in the host-enabled assembly names a writable native byte address. -/
theorem permission_pull_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    (witness : EnsembleWitness (ensemble image source auxiliary channels))
    (pulls : ∀ component ∈ auxiliary, WritePermission.Pulls component)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (address : fields 3 (ZMod p))
    (member : WritePermissionProvider.channel.pulledValue address ∈
      witness.interactionsWith WritePermissionProvider.channel.toRaw) :
    WritePermissionProvider.Permitted image address := by
  apply WritePermission.pull_permitted_of_sources image witness constraints
    (balanced _ (by simp [ensemble, ProtectedLocalCore.ensemble]))
    (component_permission_source image source auxiliary channels pulls) address
    (WritePermissionProvider.channel.pulledValue address) member rfl rfl

end SP1Clean.Soundness.HostLocalCore
