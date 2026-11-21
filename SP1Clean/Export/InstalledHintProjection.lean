import SP1Clean.Export.InstalledHintAssembly

/-! # Projection of the physical private-cursor table -/

namespace SP1Clean.Export.InstalledAssembly

open Circuit Air.Flat Soundness Semantics

variable {context : Context}

attribute [local irreducible] assembly FixedHintAssembly.assembly

private theorem prefix_components (witness : EnsembleWitness (assembly context)) (clock : BitVec 48) :
    (witness.tables.take 99).map (·.component) = (base context clock).tables := by
  rw [List.map_take, witness.tables_map_component]
  unfold assembly
  rw [← FixedHintAssembly.tables_length (context.withClock 0), List.take_left, fixed_tables context 0 clock]

/-- Retain the actual arrays in all old slots, reconstructing Clean's canonical prover data. -/
def project (witness : EnsembleWitness (assembly context)) (clock : BitVec 48) : EnsembleWitness (base context clock) :=
  EnsembleWitness.ofTables _ (witness.tables.take 99) witness.publicInput (prefix_components witness clock)

theorem project_header (witness : EnsembleWitness (assembly context)) (clock : BitVec 48) :
    (project witness clock).publicInput = witness.publicInput := rfl

/-- The literal suffix after the projected tables consists of the unique private cursor terminal. -/
theorem drop_eq_terminal (witness : EnsembleWitness (assembly context)) :
    witness.tables.drop 99 = [(terminalSlot context).table witness] := by
  have length : witness.tables.length = 100 := witness.same_length.symm.trans (tables_length context)
  rw [List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
  apply congrArg (fun value => [value])
  unfold TableSlot.table
  have index : (terminalSlot context).index.val = 99 := by
    simp only [terminalSlot, TableSlot.appendRight, TableSlot.ofIndex, Nat.add_zero, FixedHintAssembly.tables_length]
  simp only [index]

theorem project_constraints (witness : EnsembleWitness (assembly context)) (clock : BitVec 48)
    (checked : witness.Constraints) : (project witness clock).Constraints := by
  intro table member row used
  have lookup := FixedHintAssembly.component_lookups (context.withClock clock) table.component
    (EnsembleWitness.component_mem_tables_of_mem member)
  rw [project, EnsembleWitness.ofTables_tables] at member
  have mapped := List.mem_map_of_mem (f := fun t : Table Fp => (t.component, t.table)) member
  rw [withDerivedData_map] at mapped
  obtain ⟨old, retained, same⟩ := List.mem_map.mp mapped
  have component := congrArg Prod.fst same
  have rows := congrArg Prod.snd same
  change old.component = table.component at component
  change old.table = table.table at rows
  have valid := checked old (List.mem_of_mem_take retained) row (rows ▸ used)
  rw [component] at valid
  exact table.component.constraintsHold_setData lookup valid

/-- All retained physical ledger entries are evaluated at their original row values. -/
theorem project_tables_ledger (witness : EnsembleWitness (assembly context)) (clock : BitVec 48) (channel : RawChannel Fp) :
    (project witness clock).tables.flatMap (·.interactionsWith channel) ++
      ((terminalSlot context).table witness).interactionsWith channel =
        witness.tables.flatMap (·.interactionsWith channel) := by
  rw [project, EnsembleWitness.ofTables_tables, withDerivedData_interactionsWith]
  conv_rhs => rw [← List.take_append_drop 99 witness.tables, List.flatMap_append, drop_eq_terminal]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem private_clock (witness : EnsembleWitness (assembly context)) (checked : witness.Constraints) :
    ∃ clock : BitVec 48, ((terminalSlot context).table witness).interactionsWith HostHintQueue.stateChannel.toRaw =
      [HostHintQueue.stateChannel.pulledValue (context.withClock clock).finalHints,
       HostHintQueue.stateChannel.pushedValue (publicCursor context)] :=
  HostHintQueueTerminal.physical_projection 0 _ _ _ ((terminalSlot context).table_component witness)
    ((terminalSlot context).table_constraints witness checked)

theorem terminal_silent (witness : EnsembleWitness (assembly context)) {channel : RawChannel Fp}
    (other : channel ≠ HostHintQueue.stateChannel.toRaw) :
    ((terminalSlot context).table witness).interactionsWith channel = [] := by
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [(terminalSlot context).table_component witness]
  change channel ∉ [HostHintQueue.stateChannel.toRaw, HostHintQueue.stateChannel.toRaw]
  simp [other]

end SP1Clean.Export.InstalledAssembly
