import SP1Clean.Proofs.Completeness.WriteCountedRouting
import ToClean.Air.LookupFree

/-! # Shared canonical prover data for the counted WRITE tables

The circuit inputs come from the exact committed row prefixes. Changing the table map or
public input does not affect their polynomial constraints or their structural channels.
-/

namespace SP1Clean.WriteProbe.Counted
open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

theorem supply_lookupFree : (ReadbackSupply.component (p := p)).operations.lookups = [] := by
  apply Component.lookups_eq_nil_of_main
  intro input offset
  change ((ReadbackSupply.main input).operations offset).lookups = []
  simp [ReadbackSupply.main, ClockParts.circuit, ClockParts.main, circuit_norm, Gadgets.ToBits.rangeCheck,
    Gadgets.ToBits.toBits, Gadgets.ToBits.main, Gadgets.Equality.main, Operations.lookups]

theorem probe_lookupFree : (WriteProbe.component (p := p)).operations.lookups = [] := by
  apply Component.lookups_eq_nil_of_main
  intro input offset
  exact Guarded.main_lookups WriteProbe.circuit WriteProbe.guardSupported input offset

/-- A supply or read table retains its checked rows and every literal ledger when installed
at the data derived from all physical tables and their actual public input. -/
theorem at_derived_data (tables : List (Table (ZMod p))) (unique : (tables.map fun t => t.component.circuit.name).Nodup)
    (publicInput : Array (ZMod p)) (t : Table (ZMod p)) (member : t ∈ tables)
    (own : t.component = ReadbackSupply.component ∨ t.component = WriteProbe.component) (checked : t.Constraints) :
    let data := deriveProverData tables publicInput
    let rebound : Table (ZMod p) := { t with data, data_consistent := deriveTables_eq_of_mem tables unique member _ }
    rebound ∈ withDerivedData tables unique publicInput ∧ rebound.Constraints ∧ rebound.Guarantees ∧
      ∀ channel, rebound.interactionsWith channel = t.interactionsWith channel := by
  let data := deriveProverData tables publicInput
  let rebound : Table (ZMod p) := { t with data, data_consistent := deriveTables_eq_of_mem tables unique member _ }
  have empty : t.component.operations.lookups = [] := by
    rcases own with supply | probe
    · exact supply ▸ supply_lookupFree
    · exact probe ▸ probe_lookupFree
  refine ⟨List.mem_map.mpr ⟨⟨t, member⟩, List.mem_attach _ _, rfl⟩,
    fun row inTable => t.component.constraintsHold_setData empty (checked row inTable), ?_,
    Table.interactionsWith_setData t _ _⟩
  apply rebound.guarantees_iff_forall.mpr
  intro i seen _
  have declared := rebound.channel_mem_channels_of_mem_interactions i seen
  change i.channel ∈ t.component.circuit.channels at declared
  have structural (channel : RawChannel (ZMod p))
      (used : channel ∈ [readbackChannel.toRaw, versionChannel.toRaw, readChannel.toRaw])
      (weight : ZMod p) (message : Vector (ZMod p) channel.arity) : channel.Guarantees weight message data := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at used
    rcases used with rfl | rfl | rfl <;> exact fun _ => trivial
  apply structural
  rcases own with supply | probe
  · rw [supply] at declared
    change i.channel ∈ [readbackChannel.toRaw, versionChannel.toRaw] at declared
    simp only [List.mem_cons, List.not_mem_nil, or_false] at declared ⊢
    exact declared.elim Or.inl (fun h => Or.inr (Or.inl h))
  · rw [probe] at declared
    change i.channel ∈ [versionChannel.toRaw, readChannel.toRaw] at declared
    exact List.mem_cons_of_mem _ declared

end SP1Clean.WriteProbe.Counted
