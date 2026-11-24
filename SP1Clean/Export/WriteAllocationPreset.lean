import SP1Clean.Export.WriteBlockPreset
import SP1Clean.Proofs.Completeness.WriteAllocationSix

/-! # One matched six-table WRITE allocation at the installed resource preset

A single collection produces the chronological guest groups, a fixed endpoint block
provider, and the allocation open/node/seed/word tables. Both the allocation word cursor
and the block channel use the same funded physical word row at every original position.
-/

namespace SP1Clean.Export.InstalledAssembly
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation WriteEffects

/-- All six native component obligations, three private-channel matches, plus an external
block count and matching proof for this exact same generated table package. -/
structure MatchedWriteAllocation {entries : List Witness.Entry} {source target : HostState}
    (tables : Witness.SixTables entries source target) (data : ProverData Fp) : Prop extends tables.Checked data where
  /-- Total physical occurrences, counting all padding and independently guarded sites. -/
  blockBound : (tables.blockLedger data).length ≤ 7*2^27
  /-- The original block bus passes Clean's configured characteristic test. -/
  blockFit : (Balance.logUp (F := Fp)).fits (tables.blockLedger data).length = true
  /-- Each active physical block occurrence has a matching opposite occurrence. -/
  blockMatches : BalancedInteractions (tables.blockLedger data)

/-- At the fixed-provider preset, a complete admitted native execution constructs the
six real tables together. All four channel checks refer to the same funded physical word
table. Independent immutable queue readers retain their chosen counts and original values. -/
theorem fixedProviderPreset_write_allocation {ctx : Context} {events : List ExecutionEvent}
    (run : AdmissibleExecution ctx.limits SP1Prime ctx.image ctx.source ctx.target events)
    (preset : ctx.limits.LE fixedProviderPreset) (data : ProverData Fp)
    (nodeReads : HintQueue.NodeRecord Fp → Fp) (wordReads : HintQueue.WordRecord Fp → Fp) :
    let readers : Readers := ⟨nodeReads,fun _ => 0,wordReads⟩
    ∃ entries, Witness.native? ctx.image ctx.source events readers = some entries ∧
      ∃ tables : Witness.SixTables entries ctx.source.host ctx.target.host, MatchedWriteAllocation tables data := by
  intro readers
  obtain ⟨entries,collected,tables,checked⟩ := Witness.native_six_tables (run.mono (preset.trans fixedProviderPreset_le_native)) data nodeReads wordReads
  obtain ⟨bound,fit,matchAll⟩ := fixedProviderPreset_write_blocks_fit run preset readers collected checked.blocks
  exact ⟨entries,collected,tables,checked,bound,fit,matchAll⟩

end SP1Clean.Export.InstalledAssembly
