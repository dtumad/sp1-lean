import SP1Clean.Native.Operations.OrderedBoundaryVerifier
import SP1Clean.Soundness.RankedGrounding
import ToClean.Air.TransitionView
import ToClean.Air.TableBuild

/-! # Ordered inventories from the actual Clean ensemble ledger

The verifier fixes both endpoints. Every row of a registered transition component contributes
its proved unit pair; auxiliary components must omit the private control channel. Consequently
Clean channel balance, including its own count bound, gives endpoint balance of every physical
transition row. Local strict-order specifications then exclude duplicate keys and cycles.

This is the shared initialization/finalization inventory construction. Local specifications
are supplied by the enclosing ensemble's table-soundness phase; no provider uniqueness or
endpoint-permutation premise is accepted here.
-/

namespace SP1Clean.Soundness.OrderedBoundaryEnsemble

open Circuit Air.Flat RankedGrounding

variable {p : ℕ} [Fact p.Prime]

def ensemble (name : String) (initial final : Word (ZMod p))
    (views : List (TransitionView (OrderedBoundary.channel (p := p) name)))
    (auxiliary : List (Component (ZMod p))) (channels : List (RawChannel (ZMod p))) :
    Ensemble (ZMod p) unit where
  tables := views.map (·.component) ++ auxiliary
  channels := (OrderedBoundary.channel name).toRaw :: channels
  verifier := OrderedBoundaryVerifier.circuit name initial final

abbrev PhysicalRow (name : String) :=
  TransitionView (OrderedBoundary.channel (p := p) name) × Environment (ZMod p)

variable {name : String} {initial final : Word (ZMod p)}
variable {views : List (TransitionView (OrderedBoundary.channel (p := p) name))}
variable {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}

abbrev Witness := EnsembleWitness (ensemble name initial final views auxiliary channels)

def rows (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels)) :=
  TransitionView.readRows views (witness.tables.take views.length)

theorem tables_aligned (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels)) :
    List.Forall₂ (fun view table => view.component = table.component)
      views (witness.tables.take views.length) := by
  apply TransitionView.aligned_of_map_eq
  have same := congrArg (List.take views.length) witness.tables_map_component
  simpa only [← List.map_take, ensemble, List.take_left', List.length_map] using same.symm

theorem auxiliary_silent (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels) :
    (witness.tables.drop views.length).flatMap
      (·.interactionsWith (OrderedBoundary.channel name).toRaw) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have same := congrArg (List.drop views.length) witness.tables_map_component
  have componentMem : table.component ∈ auxiliary := by
    have : table.component ∈ (witness.tables.drop views.length).map (·.component) :=
      List.mem_map.mpr ⟨table, member, rfl⟩
    have mapped : (witness.tables.drop views.length).map (·.component) = auxiliary := by
      simpa only [← List.map_drop, ensemble, List.drop_left', List.length_map] using same
    rwa [mapped] at this
  rw [Table.interactionsWith_eq_filter]
  apply List.filter_eq_nil_iff.mpr
  intro interaction member equal
  have equal' : interaction.channel = (OrderedBoundary.channel name).toRaw := by simpa using equal
  exact privateChannel table.component componentMem
    (equal' ▸ table.channel_mem_channels_of_mem_interactions interaction member)

/-- This equality is derived from physical tables and circuit interfaces, not a shadow ledger. -/
theorem interactions_eq (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels) :
    witness.interactionsWith (OrderedBoundary.channel name).toRaw =
      (OrderedBoundary.channel name).transitionLedger initial final (rows witness)
        (fun row => row.1.edge row.2) := by
  rw [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons]
  have verifier : witness.verifierTable.interactionsWith (OrderedBoundary.channel name).toRaw =
      [(OrderedBoundary.channel name).pushedValue initial,
       (OrderedBoundary.channel name).pulledValue final] := by
    simp only [Table.interactionsWith, EnsembleWitness.verifierTable_flatMap,
      Operations.interactionValuesWith, EnsembleWitness.verifierTable_component,
      Ensemble.verifierTable_interactionsWith]
    change ((OrderedBoundaryVerifier.main name initial final ()).operations 0).interactionValuesWith
      (OrderedBoundary.channel name).toRaw _ = _
    exact OrderedBoundaryVerifier.interactionValues name initial final _ _ _
  rw [verifier]
  have split := List.take_append_drop views.length witness.tables
  rw [← split, List.flatMap_append, auxiliary_silent witness privateChannel, List.append_nil]
  rw [TransitionView.readRows_interactions views _ (tables_aligned witness)]
  rfl

/-- The control-channel count guard and endpoint permutation follow from actual AIR balance. -/
theorem endpointBalanced (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (balanced : BalancedInteractions (witness.interactionsWith (OrderedBoundary.channel name).toRaw)) :
    EndpointBalanced (↑(rows witness) : Multiset (PhysicalRow (p := p) name))
      (fun row => row.1.edge row.2) initial final := by
  classical
  rw [interactions_eq witness privateChannel] at balanced
  have perm := ((OrderedBoundary.channel name).transitionLedger_balanced_iff
    initial final (rows witness) (fun row => row.1.edge row.2)).mp balanced
  exact Quot.sound perm.2

/-- Every physical boundary row occurs on one exhaustive strict trail. No caller supplies its
order, coverage, or distinctness. -/
theorem exhaustiveTrail (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (balanced : BalancedInteractions (witness.interactionsWith (OrderedBoundary.channel name).toRaw))
    (strict : ∀ row ∈ rows witness, Word.toNat (row.1.edge row.2).1 < Word.toNat (row.1.edge row.2).2) :
    ExhaustiveTrail (↑(rows witness) : Multiset (PhysicalRow (p := p) name))
      (fun row => row.1.edge row.2) initial final := by
  classical
  exact exists_exhaustiveTrail_of_endpointBalanced _ _ Word.toNat initial final
    (endpointBalanced witness privateChannel balanced) strict

/-- The row environments used by the control ledger inherit their actual table specifications. -/
theorem rows_spec (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels)) (valid : witness.Spec) :
    ∀ row ∈ rows witness, row.1.component.Spec row.2 :=
  TransitionView.readRows_spec views _ (tables_aligned witness)
    (fun table member => valid table (witness.mem_allTables_of_mem_tables (List.mem_of_mem_take member)))

/-- Lift a registry's local strict-order contracts to all physical transition rows. -/
theorem rows_strict (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (strict : ∀ view ∈ views, ∀ env, view.component.Spec env →
      Word.toNat (view.edge env).1 < Word.toNat (view.edge env).2)
    (valid : witness.Spec) : ∀ row ∈ rows witness,
      Word.toNat (row.1.edge row.2).1 < Word.toNat (row.1.edge row.2).2 := by
  intro row member
  exact strict row.1 (TransitionView.readRows_view_mem _ _ row member) row.2
    (rows_spec witness valid row member)

/-- Strict local specifications and actual global balance force distinct destination ranks. -/
theorem keys_nodup_of_specs (witness : Witness (name := name) (initial := initial) (final := final)
    (views := views) (auxiliary := auxiliary) (channels := channels))
    (privateChannel : ∀ component ∈ auxiliary,
      (OrderedBoundary.channel name).toRaw ∉ component.circuit.channels)
    (strict : ∀ view ∈ views, ∀ env, view.component.Spec env →
      Word.toNat (view.edge env).1 < Word.toNat (view.edge env).2)
    (valid : witness.Spec) (balanced : witness.BalancedChannels) :
    ((rows witness).map fun row => Word.toNat (row.1.edge row.2).2).Nodup := by
  classical
  exact rankedKeys_nodup_list (rows witness) (fun row => row.1.edge row.2) Word.toNat initial final
    (endpointBalanced witness privateChannel (balanced _ (List.mem_cons_self ..)))
    (rows_strict witness strict valid)

end SP1Clean.Soundness.OrderedBoundaryEnsemble
