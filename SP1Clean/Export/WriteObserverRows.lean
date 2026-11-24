import SP1Clean.Export.WriteFundedInstallation
import SP1Clean.Export.WriteOriginalInstallation
import SP1Clean.Proofs.Completeness.WriteEffectAssembly

/-! # Local constraints and guarantees of the nineteen generated observer tables -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Machine WriteEffects.Witness
private abbrev F := ZMod SP1Prime

/-- The three generated effect consumers surrounding the fixed stream-metadata source. -/
def effectMiddle {events : List ExecutionEvent} {entries : List Entry} {streams : WriteStreams}
    (cap : EffectFits events entries streams) (data : ProverData F) (metadata : Table F) : List (Table F) :=
  [WriteEffects.requestTable ((inputs entries).dispatches.map WriteEffects.Dispatch.request) data cap.requests,
   WriteEffects.octetTable (entries.flatMap Entry.decoderRows) data cap.decoders, metadata,
   WriteEffects.dispatchTable (inputs entries).dispatches data cap.dispatches]

/-- All three dynamic effect tables satisfy their circuits and the metadata row is the counted fixed table. -/
theorem effectMiddle_valid {events : List ExecutionEvent} {entries : List Entry} {streams : WriteStreams}
    (cap : EffectFits events entries streams) (data : ProverData F) (metadata : Table F)
    (realized : cap.Realized data) (fixed : metadata.Constraints ∧ metadata.Guarantees) :
    ∀ t ∈ effectMiddle cap data metadata, t.Constraints ∧ t.Guarantees := by
  obtain ⟨request, octets, dispatch, _⟩ := realized
  intro t member
  simp only [effectMiddle, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact ⟨request.2.1, request.2.2.1⟩
  · exact ⟨octets.2.1, octets.2.2.1⟩
  · exact fixed
  · exact ⟨dispatch.2.1, dispatch.2.2.1⟩

/-- All physical tables of the observer suffix carry their own generated row checks. -/
theorem fundedSuffix_valid {entries : List Entry} {source target : ExecutionSnapshot}
    (s : SixTables entries source.host target.host) (data : ProverData F)
    (checked : s.Checked data) (early hints plans : List (Table F))
    (earlier : ∀ t ∈ early, t.Constraints ∧ t.Guarantees)
    (queue : ∀ t ∈ hints, t.Constraints ∧ t.Guarantees)
    (last : ∀ t ∈ plans, t.Constraints ∧ t.Guarantees) :
    ∀ t ∈ fundedSuffix s data early hints plans, t.Constraints ∧ t.Guarantees := by
  intro t member
  simp only [fundedSuffix, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((((head | rfl) | walk) | rfl) | plan) | (rfl | rfl | rfl | rfl)
  · exact earlier _ head
  · exact checked.blocks.placementsValid.2
  · exact queue _ walk
  · exact checked.blocks.fixedValid.2
  · exact last _ plan
  · exact checked.calls.2
  · exact checked.nodes.2
  · exact checked.seeds.2
  · exact checked.blocks.wordsValid.2

/-- Canonical installation preserves the constraints and channel guarantees of every
observer row when it rebinds the tables to the final prover data. -/
theorem installed_observer_rows {image : ProgramImage} {source target : ExecutionSnapshot}
    {final : HostHintQueue.State F} (w : EnsembleWitness (WriteSourceRegistry.base image source target final))
    (suffix : List (Table F)) (registered : suffix.map Table.component = tables source target)
    (valid : ∀ t ∈ suffix, t.Constraints ∧ t.Guarantees) :
    ∀ t ∈ (build w suffix registered).tables.drop (WriteSourceRegistry.installSources w).tables.length,
      t.Constraints ∧ t.Guarantees := by
  let pairs (q : Table F) := (q.component, q.table)
  have arrays : ((build w suffix registered).tables.drop (WriteSourceRegistry.installSources w).tables.length).map pairs =
      suffix.map pairs := by
    rw [List.map_drop]
    dsimp only [build, Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables]
    change ((withDerivedData _ _ _).map (fun q : Table F => (q.component, q.table))).drop _ = _
    rw [withDerivedData_map, List.map_append, ← List.length_map pairs (as := (WriteSourceRegistry.installSources w).tables), List.drop_left]
  intro t member
  obtain ⟨before, original, same⟩ := List.mem_map.mp (arrays ▸ List.mem_map_of_mem (f := pairs) member)
  obtain ⟨component, cells⟩ := Prod.mk.inj same
  have included : before.component ∈ tables source target := registered ▸ List.mem_map_of_mem original
  obtain ⟨constraints, guarantees, _⟩ := checks_of_original_cells component.symm cells.symm (valid before original)
    (suffix_lookupFree source target _ included) (fun i used checked => observer_guarantees_setData included i used checked)
  exact ⟨constraints, guarantees⟩

end SP1Clean.Export.WriteObservationAssembly
