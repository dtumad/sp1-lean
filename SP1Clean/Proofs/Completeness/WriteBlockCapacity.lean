import SP1Clean.Proofs.Completeness.WriteNativeBlockBalance
import ToClean.Air.DemandHeightInterval

/-! # Exact native capacity criterion for the physical WRITE block channel

Native execution bounds the three heights independently. Only their simultaneous top
rounding interval exceeds the field. The criterion is stated on the three unpadded
physical inventories and characterizes the existing signed transcript's count check.
-/

namespace SP1Clean.WriteEffects.Witness
open Circuit Air.Flat Semantics Machine FormalModel.Shard TraceGen WriteAllocation
private abbrev F := ZMod SP1Prime

/-- Whether the full physical count fits the SP1 field, using only original row counts
before the two demand paddings and the single verifier preallocation. -/
theorem block_count_iff {g w : Nat} {provider : StaticTable F StreamBlock}
    (groups : g ≤ 2^28) (words : w ≤ 2^29) (fixed : provider.height ≤ 2^29) :
    2 * WitnessGeneration.demandHeight g + 2 * WitnessGeneration.demandHeight w + provider.height < SP1Prime ↔
      g ≤ 2^27 ∨ w ≤ 2^28 ∨ provider.length ≤ 2^28 := by
  have hg := WitnessGeneration.demandHeight_le_pow groups
  have hw := WitnessGeneration.demandHeight_le_pow words
  constructor
  · intro fit
    by_contra! outside
    obtain ⟨a,b,c⟩ := outside
    have gMax := WitnessGeneration.demandHeight_of_interval (exponent := 27) a groups
    have wMax := WitnessGeneration.demandHeight_of_interval (exponent := 28) b words
    have smallExp : ¬ Nat.clog 2 provider.length ≤ 28 := by
      intro h
      exact c.not_ge ((Nat.clog_le_iff_le_pow (by decide)).mp h)
    have minHeight : 2^29 ≤ provider.height :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (show 29 ≤ Nat.clog 2 provider.length by omega)
    rw [gMax,wMax,Nat.le_antisymm fixed minHeight] at fit
    exact (show ¬ (2*2^(27+1) + 2*2^(28+1) + 2^29 < SP1Prime) by decide) fit
  · intro one
    have smallestMargin : 2*2^27 + 2*2^29 + 2^29 < SP1Prime := by decide
    rcases one with small | small | small
    · have half := WitnessGeneration.demandHeight_le_pow small
      omega
    · have half := WitnessGeneration.demandHeight_le_pow small
      omega
    · have half : provider.height ≤ 2^28 :=
        Nat.pow_le_pow_right (by decide : 0 < 2) ((Nat.clog_le_iff_le_pow (by decide)).mpr small)
      omega

/-- The exact count test for the complete funded tables of an admitted native tape.
A larger-fit claim would have to exclude simultaneous promotion of all three inventories. -/
theorem native_block_fit_iff {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : AdmissibleExecution (.native SP1Prime) SP1Prime image source target events) (readers : Readers)
    {entries : List Entry} (collected : native? image source events readers = some entries)
    {placements words fixed : Table F}
    (checked : CombinedBlocksChecked source.host target.host
      (entries.flatMap (Entry.placementGroups (.fromEndpoints source.host target.host))).length (inputs entries).words.length placements words fixed) :
    let groups := entries.flatMap (Entry.placementGroups (.fromEndpoints source.host target.host))
    let provider := blockTable (p := SP1Prime) (.fromEndpoints source.host target.host)
    let ledger := placements.interactionsWith blockChannel.toRaw ++ words.interactionsWith blockChannel.toRaw ++ fixed.interactionsWith blockChannel.toRaw
    (Balance.logUp (F := F)).fits ledger.length = true ↔
      groups.length ≤ 2^27 ∨ (inputs entries).words.length ≤ 2^28 ∨ provider.length ≤ 2^28 := by
  obtain ⟨actual,built,_,observed,_⟩ := native_inputs run readers
  cases Option.some.inj (collected.symm.trans built)
  have ticks := run.2.2.1 .ticks
  rw [run.1.2.resources_ticks] at ticks
  have small := (WriteObservations.packets_native_bound run.1.2 observed ticks (run.2.2.1 .readBytes)).2.1
  have groups : (entries.flatMap (Entry.placementGroups (.fromEndpoints source.host target.host))).length ≤ 2^28 :=
    (placementGroups_length _ entries).trans_le (small.trans (by decide))
  dsimp only
  rw [checked.occurrences]
  simpa only [Balance.logUp,decide_eq_true_eq,ComputableRingChar.char_eq,ZMod.ringChar_zmod_n] using
    (block_count_iff groups (native_word_capacity run readers collected) (admissible_fixed_heights run).1)

end SP1Clean.WriteEffects.Witness
