import SP1Clean.Export.FixedRamCapacity
import SP1Clean.Soundness.Shard.Contract
import SP1CleanTest.Alignment.Core.LargeRamIdentity

/-! # Fixed RAM provider heights for constant and alternating native release identities -/

namespace SP1CleanTest.FixedRamCapacity
open SP1Clean SP1Clean.Semantics SP1Clean.FormalModel.Shard SP1Clean.Export.InstalledAssembly

/-- A run of 2^29 equal live bytes gives three intervals in the native address window.
The verifier-fixed RAM provider pads them to exactly four rows. -/
theorem empty_large_ram_provider_height :
    ∃ image source commitments,
      ReleaseStatementExecution (ResourceLimits.native SP1Prime) SP1Prime commitments image source source [] ∧
      (source.sail.memory.supportBelow NativeLayout.sailMemory.upper).card = 2 ^ 29 ∧
      ∀ name : String, (InitialMemoryLookup.membership (p := SP1Prime) source.sail.memory
        NativeLayout.sailMemory.upper name).height = 4 := by
  obtain ⟨image, source, commitments, execution, support, changes⟩ := empty_large_ram
  refine ⟨image, source, commitments, execution, support, fun name => ?_⟩
  rw [InitialMemoryLookup.membership_height, ByteMemory.intervals_length, changes]
  decide

/-- One alternating identity meets the complete native release domain and has no installed raw LogUp witness
at any public header or heights. A complete compiler for this ensemble and context cannot exist. -/
theorem empty_release_without_raw_statement :
    ∃ context : Context, context.source = context.target ∧ context.limits = ResourceLimits.native SP1Prime ∧
      ReleaseStatementExecution context.limits SP1Prime context.commitments context.image
        context.source context.target [] ∧
      (∀ (header : SP1PublicIO Fp) heights, ¬ (assembly context).Statement .logUp header heights) ∧
        ¬ Nonempty (Soundness.Shard.CompilerTarget (assembly context) context.limits context.commitments
          context.image context.source context.target) := by
  obtain ⟨image, source, commitments, execution, changes⟩ := empty_alternating_ram
  let context : Context := ⟨image, source, source, commitments, .native SP1Prime⟩
  have denied := not_statement_of_target_ram_changes context changes.le
  refine ⟨context, rfl, rfl, execution, denied, ?_⟩
  rintro ⟨compiler⟩
  have actual := executes_iff.mp execution.1.1.1
  obtain ⟨heights, _, accepted⟩ := compiler.completeness (SP1StateBoundary.ofExecution context.source context.target context.commitments)
    ⟨[], actual.2, rfl, actual.1, execution.1.1.2, execution.1.2, execution.2⟩
  exact denied _ heights accepted

end SP1CleanTest.FixedRamCapacity
