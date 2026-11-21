import SP1Clean.Export.FixedRamCapacity
import SP1Clean.Soundness.Shard.Contract
import SP1CleanTest.Alignment.Core.LargeRamIdentity

/-! # An empty release execution beyond the installed fixed RAM capacity -/

namespace SP1CleanTest.FixedRamCapacity
open SP1Clean SP1Clean.Semantics SP1Clean.FormalModel.Shard SP1Clean.Export.InstalledAssembly

/-- One identity meets the complete native release domain and has no installed raw LogUp witness
at any public header or heights. A complete compiler for this ensemble and context cannot exist. -/
theorem empty_release_without_raw_statement :
    ∃ context : Context, context.source = context.target ∧ context.limits = ResourceLimits.native SP1Prime ∧
      ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
        context.source context.target [] ∧
      ∀ header : SP1PublicIO Fp, (∀ heights, ¬ (assembly context).Statement .logUp header heights) ∧
        ¬ Nonempty (Soundness.Shard.CompilerTarget (assembly context) context.limits context.commitments
          context.image context.source context.target header) := by
  obtain ⟨image, source, commitments, execution, support⟩ := empty_large_ram
  let context : Context := ⟨image, source, source, commitments, .native SP1Prime⟩
  refine ⟨context, rfl, rfl, execution, fun header => ?_⟩
  have denied := not_statement_of_target_ram_support context support.ge header
  refine ⟨denied, ?_⟩
  rintro ⟨compiler⟩
  have actual := executes_iff.mp execution.1.1.1
  obtain ⟨heights, _, accepted⟩ := compiler.completeness header
    ⟨[], actual.2, rfl, actual.1, execution.1.1.2, execution.1.2, execution.2⟩
  exact denied heights accepted

end SP1CleanTest.FixedRamCapacity
