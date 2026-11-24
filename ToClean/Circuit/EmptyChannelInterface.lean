module

public import Clean.Circuit.Subcircuit

/-! # Empty interaction lists from an empty declared circuit interface

Clean proves that every emitted interaction channel is declared. The corresponding empty-list
corollary lets callers account for channel-free arithmetic without expanding its structure.
-/

@[expose] public section

namespace FormalCircuitBase
open Circuit

variable {F : Type} [FiniteField F] {I O : TypeMap} [ProvableType I] [ProvableType O]

theorem interactions_eq_nil_of_channels_eq_nil (c : FormalCircuitBase F I O)
    (empty : c.channels = []) (input : Var I F) (n : Nat) : ((c.main input).operations n).interactions = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro i member
  have declared := c.channels_subset input n (List.mem_map_of_mem (f := AbstractInteraction.channel) member)
  change i.channel ∈ c.channels at declared
  rw [empty] at declared
  exact List.not_mem_nil declared

end FormalCircuitBase
