import SP1Clean.Export.InstalledAssembly
import SP1Clean.Proofs.Completeness.HintQueueTerminal

/-! # Extending a fixed-cursor host witness with its physical terminal -/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Semantics Soundness HostHintQueueTerminal
open HostHintQueue (stateChannel)
open scoped Classical

variable {context : Context} {clock : BitVec 48}

private abbrev terminalTable (w : EnsembleWitness (base context clock)) :=
  tableFor (publicCursor context) clock w.data

private theorem allComponents (w : EnsembleWitness (base context clock)) :
    (w.tables ++ [terminalTable w]).map (·.component) = (assembly context).tables := by
  simp only [List.map_append, List.map_cons, List.map_nil, w.tables_map_component,
    fixed_tables context clock 0]
  rfl

/-- Append the honest private clock row and reconstruct canonical data over all physical slots. -/
def extend (w : EnsembleWitness (base context clock)) : EnsembleWitness (assembly context) :=
  EnsembleWitness.ofTables _ (w.tables ++ [terminalTable w]) w.publicInput (allComponents w)

private theorem extend_heights (w : EnsembleWitness (base context clock)) :
    (extend w).heights = w.heights ++ [1] := by
  simp only [extend, EnsembleWitness.heights, EnsembleWitness.ofTables_tables]
  change List.map (fun t : Table Fp => t.table.length) (withDerivedData _ _ _) = _
  rw [show (fun t : Table Fp => t.table.length) = List.length ∘ Table.table by rfl, ← List.map_map,
    withDerivedData_map_table, List.map_append, List.map_append, List.map_map]
  rfl

attribute [local irreducible] assembly FixedHintAssembly.assembly

private theorem extend_checked (w : EnsembleWitness (base context clock)) (valid : w.Constraints) : (extend w).Constraints := by
  intro table member row used
  have known := EnsembleWitness.component_mem_tables_of_mem member
  have lookup : table.component.operations.lookups = [] := by
    refine List.eq_nil_iff_forall_not_mem.mpr fun lookup occurs => ?_
    obtain ⟨record, covered, _⟩ := (description context).lookups_complete table.component known lookup occurs
    exact List.not_mem_nil covered
  rw [extend, EnsembleWitness.ofTables_tables] at member
  have mapped := List.mem_map_of_mem (f := fun t : Table Fp => (t.component, t.table)) member
  rw [withDerivedData_map] at mapped
  obtain ⟨old, retained, same⟩ := List.mem_map.mp mapped
  have component := congrArg Prod.fst same
  have rows := congrArg Prod.snd same
  change old.component = table.component at component
  change old.table = table.table at rows
  have checked : old.Constraints := by
    rcases List.mem_append.mp retained with original | terminal
    · exact valid old original
    · obtain rfl := List.mem_singleton.mp terminal
      exact (tableFor_valid ..).1
  have ok := checked row (rows ▸ used)
  rw [component] at ok
  exact table.component.constraintsHold_setData lookup ok

private theorem terminal_ledger (w : EnsembleWitness (base context clock)) (channel : RawChannel Fp) :
    (terminalTable w).interactionsWith channel =
      (if channel = stateChannel.toRaw then
        [stateChannel.pulledValue (context.withClock clock).finalHints, stateChannel.pushedValue (publicCursor context)]
       else []) := by
  split_ifs with same
  · subst channel
    exact tableFor_ledger 0 _ _ clock w.data
  · apply Table.interactionsWith_nil_of_channel_not_mem
    change channel ∉ [stateChannel.toRaw, stateChannel.toRaw]
    simp [same]

private theorem tableLedger (w : EnsembleWitness (base context clock)) (channel : RawChannel Fp) :
    (extend w).tables.flatMap (·.interactionsWith channel) =
      w.tables.flatMap (·.interactionsWith channel) ++ (terminalTable w).interactionsWith channel := by
  simp only [extend, EnsembleWitness.ofTables_tables, withDerivedData_interactionsWith, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]

private theorem extend_ledgers (w : EnsembleWitness (base context clock)) (channel : RawChannel Fp) :
    ∃ first last : List (Interaction Fp),
      w.interactionsWith channel = first ++ (if channel = stateChannel.toRaw then
        [stateChannel.pulledValue (context.withClock clock).finalHints] else []) ++ last ∧
      (extend w).interactionsWith channel = first ++ (if channel = stateChannel.toRaw then
        [stateChannel.pulledValue (publicCursor context)] else []) ++ last ++
        (if channel = stateChannel.toRaw then [stateChannel.pulledValue (context.withClock clock).finalHints,
          stateChannel.pushedValue (publicCursor context)] else []) := by
  let env := w.data.publicEnvironment
  obtain ⟨first, after, vary⟩ := verifier_split context env channel
  have start : w.verifierInteractionsWith channel =
      (base context clock).verifierOperations.interactionValuesWith channel env := rfl
  have finish : (extend w).verifierInteractionsWith channel =
      (base context 0).verifierOperations.interactionValuesWith channel env := by
    unfold EnsembleWitness.verifierInteractionsWith assembly
    exact Operations.interactionValuesWith_congr rfl
  refine ⟨first, after ++ w.tables.flatMap (·.interactionsWith channel), ?_, ?_⟩
  · change w.verifierInteractionsWith channel ++ w.tables.flatMap _ = _
    rw [start, vary clock, List.append_assoc]
  · change (extend w).verifierInteractionsWith channel ++ (extend w).tables.flatMap _ = _
    rw [finish, vary 0, tableLedger, terminal_ledger]
    simp only [List.append_assoc, publicCursor]

private theorem extend_balanced (w : EnsembleWitness (base context clock)) (old : w.Balanced .logUp) :
    (extend w).Balanced .logUp := by
  intro channel registered
  have present : channel ∈ (base context clock).channels := by
    rw [fixed_channels context clock 0]
    unfold assembly at registered
    exact registered
  have funds := old channel present
  obtain ⟨first, last, prior, extended⟩ := extend_ledgers w channel
  change LogUpBalanced (w.interactionsWith channel) at funds
  change LogUpBalanced ((extend w).interactionsWith channel)
  rw [prior] at funds
  rw [extended]
  by_cases same : channel = stateChannel.toRaw
  · simp only [ite_eq_left same] at funds ⊢
    exact (cancel_terminal first last (publicCursor context) (context.withClock clock).finalHints).mpr funds
  · simpa only [ite_eq_right same, List.append_nil] using funds

/-- The full occurrence count includes both terminal messages, also when the keys coincide. -/
theorem extend_count (w : EnsembleWitness (base context clock)) (channel : RawChannel Fp) :
    ((extend w).interactionsWith channel).length = (w.interactionsWith channel).length +
      (if channel = stateChannel.toRaw then 2 else 0) := by
  obtain ⟨first, last, prior, extended⟩ := extend_ledgers w channel
  rw [prior, extended]
  split_ifs <;> simp only [List.length_append, List.length_cons, List.length_nil]

private theorem cursorRegistered (context : Context) :
    stateChannel.toRaw ∈ (assembly context).channels := by
  have member : HostHintQueueTerminal.component (publicCursor context) ∈ (assembly context).tables := by
    unfold assembly
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  exact (assembly context).tables_channels _ member (List.mem_cons_self ..)

private theorem capacity_iff (w : EnsembleWitness (base context clock))
    (fit : (base context clock).interactionsFit .logUp w.heights) :
    (assembly context).interactionsFit .logUp (w.heights ++ [1]) ↔
      (base context clock).interactionCount (stateChannel (p := SP1Prime)).toRaw.name w.heights + 2 < ringChar Fp := by
  rw [← extend_heights w, (extend w).interactionsFit_iff]
  have registry : (base context clock).channels = (assembly context).channels := by
    unfold assembly
    exact fixed_channels context clock 0
  have here := cursorRegistered context
  have there := registry.symm ▸ here
  have prior := (w.interactionsFit_iff .logUp).mp fit
  constructor
  · intro actual
    have h := actual _ here
    simpa only [Balance.logUp, ComputableRingChar.char_eq, decide_eq_true_eq, extend_count,
      ite_true, w.length_interactionsWith there] using h
  · intro enough channel member
    have oldMember := registry.symm ▸ member
    rw [extend_count]
    by_cases same : channel = stateChannel.toRaw
    · subst channel
      simpa only [Balance.logUp, ComputableRingChar.char_eq, decide_eq_true_eq, ite_true,
        w.length_interactionsWith there] using enough
    · simpa only [ite_eq_right same, Nat.add_zero] using prior channel oldMember

/-- Any accepted 99-slot projection supplies the original physical arrays needed by the installed
assembly. The installed relation checks the capacity of the complete inventory, including both terminal
interactions on the queue state channel. -/
theorem statement_of_fixedCursor (context : Context) (clock : BitVec 48) {header : SP1PublicIO Fp} {heights : List ℕ}
    (accepted : (base context clock).Statement .logUp header heights)
    (capacity : (assembly context).interactionsFit .logUp (heights ++ [1])) :
    (assembly context).Statement .logUp header (heights ++ [1]) := by
  obtain ⟨_, w, publicEq, sizes, valid, funded⟩ := accepted
  exact ⟨capacity, extend w, publicEq, (extend_heights w).trans (congrArg (· ++ [1]) sizes),
    extend_checked w valid, extend_balanced w funded⟩

private theorem heights_terminal (w : EnsembleWitness (assembly context)) :
    w.heights = w.heights.take 99 ++ [1] := by
  let t := (terminalSlot context).table w
  have suffix : w.tables.drop 99 = [t] := drop_eq_terminal w
  obtain ⟨row, fixed⟩ := HostHintQueueTerminal.one_physical_row t ((terminalSlot context).table_component w)
  have height : t.length = 1 := by change t.table.length = 1; rw [fixed]; rfl
  have shape := congrArg (List.map Table.length) (List.take_append_drop 99 w.tables)
  simpa only [EnsembleWitness.heights, List.map_append, List.map_take, suffix, List.map_cons, List.map_nil, height] using shape.symm

/-- The two native raw statements are related in both directions at every public height vector.
The physical height and occurrence checks remain the exact checks of the installed layout. -/
private theorem statement_iff_capacity (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ} :
    (assembly context).Statement .logUp header heights ↔
      (assembly context).interactionsFit .logUp heights ∧ heights = heights.take 99 ++ [1] ∧
        ∃ clock : BitVec 48, (base context clock).Statement .logUp header (heights.take 99) := by
  constructor
  · intro accepted
    have projected := project_statement context accepted
    obtain ⟨fit, w, _, sizes, _, _⟩ := accepted
    exact ⟨fit, sizes ▸ heights_terminal w, projected⟩
  · rintro ⟨fit, shape, clock, accepted⟩
    exact shape.symm ▸ statement_of_fixedCursor context clock accepted (shape ▸ fit)

/-- At the projected heights exactly two physical occurrences on the queue channel are added.
Every other registered channel inherits its original capacity, including zero-weight rows. -/
theorem statement_iff_fixedCursor (context : Context) {header : SP1PublicIO Fp} {heights : List ℕ} :
    (assembly context).Statement .logUp header heights ↔
      heights = heights.take 99 ++ [1] ∧ ∃ clock : BitVec 48,
        (base context clock).Statement .logUp header (heights.take 99) ∧
        (base context clock).interactionCount (stateChannel (p := SP1Prime)).toRaw.name (heights.take 99) + 2 < ringChar Fp := by
  rw [statement_iff_capacity]
  constructor
  · rintro ⟨cap, shape, clock, accepted⟩
    refine ⟨shape, clock, accepted, ?_⟩
    obtain ⟨fit, w, _, sizes, _, _⟩ := accepted
    have extended : (assembly context).interactionsFit .logUp (w.heights ++ [1]) := by
      rw [sizes, ← shape]
      exact cap
    rw [← sizes]
    exact (capacity_iff w (sizes.symm ▸ fit)).mp extended
  · rintro ⟨shape, clock, accepted, bound⟩
    refine ⟨?_, shape, clock, accepted⟩
    obtain ⟨fit, w, _, sizes, _, _⟩ := accepted
    rw [shape, ← sizes]
    exact (capacity_iff w (sizes.symm ▸ fit)).mpr (sizes ▸ bound)

end SP1Clean.Export.InstalledAssembly
