import SP1Clean.Native.Operations.HostExitBoundary
import ToClean.Air.Footprint
import ToClean.Air.TableBuild

/-! # Public verifier boundary regressions

A stopped source cannot change its exit word, even when the receipt selector is zero. Installing
the boundary preserves the committed table and its canonical data. The disabled receipt remains
an occurrence, and the assertion contributes its own pull/push pair.
-/

namespace SP1CleanTest.VerifierBoundary
open Circuit Air.Flat
open SP1Clean

private abbrev Fp := ZMod 7
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def physical : Table Fp where
  component := {
    circuit := { GeneralFormalCircuit.empty Fp (fields 1) with name := "retained" }
    generation := .demand {
      channel := ({ name := "fixture", Guarantees _ _ := True } : Channel Fp unit)
      trigger := .pull
      guard _ := .false
      input _ := pure #v[0]
    } }
  table := [#[3]]
  data := { tables := fun name arity =>
    if name = "retained" then #[rowPrefix arity #[3]] else #[], publicInput := #[] }
  data_consistent := rfl
  length_le := by decide
  uniform_width := by
    intro row member
    obtain rfl := List.mem_singleton.mp member
    rfl
  fixed_rows_match := by trivial

private def base : Ensemble Fp unit where
  tables := [physical.component]
  unique_names := by simp
  channels := [HostExitBoundary.channel.toRaw]
  unique_channel_names := by simp
  tables_channels := by
    intro component member
    obtain rfl := List.mem_singleton.mp member
    change [] ⊆ _
    simp
  verifier_channels := by simp [Verifier.Program.channels, Verifier.Program.channelsWithGuarantees,
    Verifier.Program.channelsWithRequirements, Verifier.Program.operations, circuit_norm]

private def original : EnsembleWitness base :=
  EnsembleWitness.ofTables base [physical] () rfl

private theorem registered (source target : Option (BitVec 32)) :
    (HostExitBoundary.closed (p := 7) source target).circuit.channels ⊆ base.channels := by
  simp [base, HostExitBoundary.closed, HostExitBoundary.circuit, circuit_norm]

private def candidate (source target : Option (BitVec 32)) :
    EnsembleWitness ((HostExitBoundary.closed source target).install base (registered source target)) :=
  EnsembleWitness.ofTables _ [physical] () rfl

/-- Installing verifier checks never adds the old synthetic singleton to physical rows. -/
theorem samePhysicalRows (source target : Option (BitVec 32)) :
    (candidate source target).tables = original.tables := rfl

/-- Canonical data remains identical at every name and arity, including the retained input row. -/
theorem sameCanonicalData (source target : Option (BitVec 32)) :
    (candidate source target).data = original.data := rfl

/-- The added assertion always contributes two occurrences, even when its value is zero. -/
theorem assertionOccurrences (source target : Option (BitVec 32)) :
    (candidate source target).channelOccurrences ((HostExitBoundary.closed source target).channel base) = 2 := by
  rw [ClosedVerifier.installed_channelOccurrences]
  simp [ClosedVerifier.operations, HostExitBoundary.closed, HostExitBoundary.circuit,
    HostExitBoundary.main, circuit_norm]

/-- Stopped-to-stopped changes fail the actual verifier balance condition, despite a zero receipt selector. -/
theorem changedStoppedStatusRejected :
    ¬ (candidate (some 1) (some 2)).BalancedChannels := by
  intro balanced
  have checked := ((HostExitBoundary.closed (p := 7) (some 1) (some 2)).balanced_iff
    (candidate (some 1) (some 2))).mp balanced |>.2
  norm_num [ClosedVerifier.Checks, ClosedVerifier.operations, HostExitBoundary.closed,
    HostExitBoundary.circuit, HostExitBoundary.main, circuit_norm] at checked

/-- A running boundary with no exit keeps the disabled receipt in the literal ledger. -/
theorem disabledReceiptOccurrence :
    ((candidate none none).interactionsWith (HostExitBoundary.channel (p := 7)).toRaw).length = 1 := by
  have different : (HostExitBoundary.closed (p := 7) none none).channel base ≠
      HostExitBoundary.channel.toRaw := by
    intro same
    apply (HostExitBoundary.closed (p := 7) none none).channel_not_mem base
    rw [same]
    simp [base]
  rw [← ClosedVerifier.interactionView_interactions _ _ _ different]
  have permutation := (HostExitBoundary.closed (p := 7) none none).interactionView_interactions_perm
    (candidate none none) HostExitBoundary.channel.toRaw
  have original_empty : ((HostExitBoundary.closed (p := 7) none none).project
      (candidate none none)).interactionsWith HostExitBoundary.channel.toRaw = [] := by
    change original.interactionsWith HostExitBoundary.channel.toRaw = []
    rw [EnsembleWitness.interactionsWith_of_verifier_empty rfl]
    change (withDerivedData [physical] (by simp) #[]).flatMap (·.interactionsWith HostExitBoundary.channel.toRaw) = []
    rw [withDerivedData_interactionsWith]
    change physical.interactionsWith HostExitBoundary.channel.toRaw ++ [] = []
    rw [List.append_nil]
    simp only [Table.interactionsWith, Operations.interactionValuesWith, Component.interactionsWith_eq]
    simp [physical, Component.rowOperations, GeneralFormalCircuit.empty, circuit_norm]
  rw [permutation.length_eq, List.length_append, original_empty, List.length_nil, Nat.zero_add]
  change (((HostExitBoundary.main none none ()).operations 0).interactionValuesWith _ _).length = _
  rw [HostExitBoundary.values]
  simp

end SP1CleanTest.VerifierBoundary
