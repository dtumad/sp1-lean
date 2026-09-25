import SP1Clean.Soundness.ResourceEnsemble
import ToClean.Air.Footprint

/-! # Physical resource consumers for the installed native assembly

Count the actual assembly, including host resource tables and the singleton verifier. The silent
endpoint checker preserves the complete physical inventory in both directions. Raw acceptance
supplies every registered channel's native field-count ceiling. Tighter independent ceilings and
full mixed construction demand remain A4/A5/A6 obligations; they are not capstone caller premises.
-/

namespace SP1Clean.Soundness.ResourceEnsemble
open Circuit Air.Flat Model.Core Machine

variable {p : ℕ} [Fact p.Prime]

/-- The installed checker preserves both numeric physical budgets exactly. -/
theorem physicalFits_iff {limits : ResourceLimits} {source target : ExecutionSnapshot}
    {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness (install limits source target base)) :
    witness.PhysicalFits limits.tableRows limits.channelOccurrences ↔
      ((ResourceBoundary.checker limits source target).project witness).PhysicalFits
        limits.tableRows limits.channelOccurrences :=
  ((ResourceBoundary.checker limits source target).project_physicalFits witness _ _).symm

/-- Every registered ledger of an accepted witness satisfies the native inclusive field ceiling.
This covers arbitrary installed host/boundary channels rather than a selected channel enum. -/
theorem accepted_channel_budget {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness base) (balanced : witness.BalancedChannels) :
    ∀ channel ∈ base.channels,
      witness.channelOccurrences channel ≤ (ResourceLimits.native p).channelOccurrences := by
  have capacity : witness.ChannelCapacity p := by
    simpa only [ZMod.ringChar_zmod_n] using witness.channelCapacity_of_balanced balanced
      (by simpa only [ZMod.ringChar_zmod_n] using (Fact.out : p.Prime).pos)
  intro channel member
  have bound := capacity channel member
  change _ ≤ p - 1
  omega

/-- Any table emitting into a registered channel inherits its physical height bound, even with
inactive rows. A silent table needs a separate height check; balance cannot bound it. -/
theorem accepted_table_budget {base : Ensemble (ZMod p) SP1PublicIO}
    (witness : EnsembleWitness base) (balanced : witness.BalancedChannels)
    {table : Table (ZMod p)} (member : table ∈ witness.allTables)
    {channel : RawChannel (ZMod p)} (registered : channel ∈ base.channels)
    (emits : 0 < table.component.channelWidth channel) :
    table.length ≤ (ResourceLimits.native p).tableRows :=
  (witness.table_length_le_occurrences member channel emits).trans
    (accepted_channel_budget witness balanced channel registered)

/-- A constructed base witness retains its exact physical budgets when the semantic endpoint
checks are installed. No row, provider occurrence or host resource is dropped by the adapter. -/
theorem lift_physicalFits {limits : ResourceLimits} {source target : ExecutionSnapshot}
    {base : Ensemble (ZMod p) SP1PublicIO} (witness : EnsembleWitness base)
    (fits : witness.PhysicalFits limits.tableRows limits.channelOccurrences) :
    ((ResourceBoundary.checker limits source target).lift witness).PhysicalFits
      limits.tableRows limits.channelOccurrences :=
  ((ResourceBoundary.checker limits source target).project_physicalFits _ _ _).mp fits

/-- Resource installation constructs a valid witness with the same physical capacity from an
admissible semantic endpoint and an already-built base witness. Remaining mixed assembly belongs
to A6; this theorem discharges the adapter's whole contribution. -/
theorem lift_of_admissible {limits : ResourceLimits} {image : ProgramImage}
    {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    {base : Ensemble (ZMod p) SP1PublicIO} (witness : EnsembleWitness base)
    (execution : FormalModel.Shard.AdmissibleExecution limits p image source target events)
    (clock : ResourceBoundary.ClockFor target witness.publicInput)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (fits : witness.PhysicalFits limits.tableRows limits.channelOccurrences) :
    let lifted := (ResourceBoundary.checker limits source target).lift witness
    lifted.Constraints ∧ lifted.BalancedChannels ∧
      lifted.PhysicalFits limits.tableRows limits.channelOccurrences := by
  exact ⟨(ResourceBoundary.checker limits source target).lift_constraints witness constraints
      (checks_of_admissible execution clock witness.data),
    (ResourceBoundary.checker limits source target).lift_balanced witness balanced,
    lift_physicalFits witness fits⟩

end SP1Clean.Soundness.ResourceEnsemble
