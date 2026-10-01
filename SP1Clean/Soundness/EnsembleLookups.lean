import SP1Clean.Soundness.SP1Ensemble
import ToClean.Air.TableBuild

/-! # Constraint transport for the native instruction/provider inventory

The instruction components have no lookups. Provider lookups use only Clean's fixed byte-XOR
table, whose membership ignores prover data. Their physical constraints therefore survive a
change from witness-generation data to the data derived from the committed tables.

This says nothing about data-dependent channel guarantees, semantic commitment bindings or
arbitrary ensembles with dynamic lookups; those require their own agreement proofs.
-/

namespace SP1Clean.Soundness

open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

private theorem provider_lookup_contains_setData (id : ProviderTableId)
    (row : Array (ZMod p)) (data data' : ProverData (ZMod p))
    (lookup : Lookup (ZMod p)) (member : lookup ∈ (providerTableFor id).operations.lookups) :
    lookup.Contains (Environment.fromArray row data) →
      lookup.Contains (Environment.fromArray row data') := by
  have eval_eq : Expression.eval (Environment.fromArray row data) =
      Expression.eval (Environment.fromArray row data') :=
    funext fun expression => Expression.eval_congr
      (env := Environment.fromArray row data) (env' := Environment.fromArray row data')
      rfl expression
  cases id with
  | byte provider =>
    cases provider <;>
      simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
        ByteChip.U8Range.circuit, ByteChip.MSB.circuit, ByteChip.AndByte.circuit,
        ByteChip.OrByte.circuit, ByteChip.XorByte.circuit, ByteChip.Ltu.circuit,
        ByteChip.U8Range.main, ByteChip.MSB.main, ByteChip.AndByte.main,
        ByteChip.OrByte.main, ByteChip.XorByte.main, ByteChip.Ltu.main,
        Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits,
        Gadgets.And.And8.circuit, Gadgets.And.And8.main,
        Gadgets.Or.Or8.circuit, Gadgets.Or.Or8.main, circuit_norm] at member
    all_goals subst lookup
    all_goals
      simp only [Lookup.Contains, eval_eq, Gadgets.Xor.ByteXorTable, _root_.Table.toRaw,
        _root_.Table.fromStatic, StaticTable.toTable]
      exact fun h => h
  | range width =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      RangeChip.circuitFor, RangeChip.circuit, circuit_norm] at member
  | program =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      ProgramProviderChip.circuit, ProgramProviderChip.main,
      Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, circuit_norm] at member
  | memoryInit =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryProviderChip.circuit, MemoryProviderChip.main, WordRangeCheck.circuit, circuit_norm] at member
  | memoryFinalize =>
    simp [providerTableFor, Component.lookups_eq, Component.rowOperations,
      MemoryFinalizeChip.circuit, MemoryFinalizeChip.main, circuit_norm] at member
  | memoryBump => simp [providerTableFor, MemoryBumpChip.lookups_empty] at member
  | stateBump => simp [providerTableFor, StateBumpChip.lookups_empty] at member
  | halt => simp [providerTableFor, HaltChip.lookups_empty] at member
  | syscallInstrs => simp [providerTableFor, SyscallInstrsChip.lookups_empty] at member

/-- Every native provider constraint depends on its cells and fixed tables alone. -/
theorem providerTableFor_constraints_setData (id : ProviderTableId)
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : (providerTableFor id).operations.ConstraintsHold (Environment.fromArray row data)) :
    (providerTableFor id).operations.ConstraintsHold (Environment.fromArray row data') :=
  Operations.constraintsHold_congr (env := Environment.fromArray row data)
    (env' := Environment.fromArray row data') rfl
    (provider_lookup_contains_setData id row data data') checked

/-- Generated rows of this inventory may be checked at the ensemble's canonical data. -/
theorem sp1Table_constraints_setData (component : Component (ZMod p))
    (member : component ∈ (sp1Ensemble (p := p)).tables)
    {row : Array (ZMod p)} {data data' : ProverData (ZMod p)}
    (checked : component.operations.ConstraintsHold (Environment.fromArray row data)) :
    component.operations.ConstraintsHold (Environment.fromArray row data') := by
  rw [sp1Ensemble_tables] at member
  rcases List.mem_append.mp member with instruction | provider
  · exact component.constraintsHold_setData (sp1Tables_lookups_empty component instruction) checked
  · obtain ⟨id, _, rfl⟩ := List.mem_map.mp provider
    exact providerTableFor_constraints_setData id checked

end SP1Clean.Soundness
