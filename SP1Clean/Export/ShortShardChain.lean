import SP1Clean.Export.ShortShard
import SP1Clean.Export.ShardChain

/-! # Composing short native shards

Every piece of an accepted chain with public clock intervals shorter than sixteen ticks
satisfies its complete release statement. Their tapes concatenate to one authenticated
execution, preserving native encodings at the joined cuts. The bounds belong to each shard.
-/

namespace SP1Clean.Export.InstalledAssembly

open Semantics Machine FormalModel.Shard

/-- Short public statements compose with independently checked per-shard limits. The paired
tapes retain the complete release statements and identify the labels of the concatenated path. -/
theorem AcceptedChain.short_release {image : ProgramImage} {commitments : CommitmentStatement}
    {source target : ExecutionSnapshot} {shards : List LocalStatement}
    (accepted : AcceptedChain image commitments source shards target)
    (short : ∀ shard ∈ shards, shard.context.limits = ResourceLimits.native SP1Prime ∧
      clkNat shard.header.final_clk_high shard.header.final_clk_low -
        clkNat shard.header.init_clk_high shard.header.init_clk_low < 16) :
    ∃ tapes : List (List ExecutionEvent),
      List.Forall₂ (fun shard events => ExecutionFacts shard.context shard.header events ∧
        (events = [] ∨ events = [.ordinary]) ∧
        ReleaseStatementExecution shard.context.limits SP1Prime commitments image
          shard.context.source shard.context.target events) shards tapes ∧
      (sp1Machine SP1Prime image).Trace source.realize tapes.flatten target.realize ∧
      ExecutionPath.Encoded (policy SP1Prime image) image.program source.realize tapes.flatten ∧
      ExecutionPath.ReleaseLinks (policy SP1Prime image) image.program source.realize tapes.flatten ∧
      commitments.Matches tapes.flatten := by
  induction shards generalizing source with
  | nil =>
    have same := (ExecutionSnapshot.equivalent_iff source target).mp accepted
    exact ⟨[], .nil, trace_iff_executionPath.mpr (ExecutionPath.nil_iff.mpr same.symm),
      ExecutionPath.encoded_nil, ExecutionPath.releaseLinks_nil, commitments.matches_nil⟩
  | cons shard rest ih =>
    obtain ⟨imageEq, commitmentsEq, joined, raw, remaining⟩ := accepted
    obtain ⟨native, interval⟩ := short shard List.mem_cons_self
    obtain ⟨xs, facts, shape, statement⟩ := native_release_of_short_statement shard.context native interval raw
    obtain ⟨ys, pieces, tailTrace, tailEncoded, tailLinks, tailDecl⟩ :=
      ih remaining (fun next member => short next (List.mem_cons_of_mem _ member))
    have same := (ExecutionSnapshot.equivalent_iff _ _).mp joined
    rw [imageEq, commitmentsEq] at statement
    have left := statement.1.1.1.2
    have encoded := statement.1.1.2.1
    have links := statement.1.2
    rw [← same] at left encoded links
    exact ⟨xs :: ys, .cons ⟨facts, shape, statement⟩ pieces,
      trace_iff_executionPath.mpr (left.append (trace_iff_executionPath.mp tailTrace)),
      (ExecutionPath.encoded_append_iff left).mpr ⟨encoded, tailEncoded⟩,
      (ExecutionPath.releaseLinks_append_iff left).mpr ⟨links, tailLinks⟩,
      (commitments.matches_append _ _).mpr ⟨statement.2.2, tailDecl⟩⟩

end SP1Clean.Export.InstalledAssembly
