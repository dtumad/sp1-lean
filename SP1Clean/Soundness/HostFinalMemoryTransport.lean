import SP1Clean.Soundness.HostFinalMemoryLedger

/-! # Exact channel transport to the installed target Memory checks

Only the five registered boundary tables and the fixed verifier demand use these private
protocols. The projection retains every occurrence, including disabled selection entries,
so it transports both integer balance and the original count bounds.
-/

namespace SP1Clean.Soundness.HostFinalMemory

open Circuit Air.Flat Channels Model.Core
open scoped Classical

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot} {target : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState}
  {others : List (HostLocalHandoff.Receiver (p := p))} {resources : List (Component (ZMod p))}
  {channels : List (RawChannel (ZMod p))}

private theorem checkSlot_position (index : Fin 2) :
    (checkSlot (image := image) (source := source) (target := target) (final := final)
      (bankFinal := bankFinal) (others := others) (resources := resources) (channels := channels) index).index.val =
      (beforeChecks image source others resources).length + index.val := by
  simp only [checkSlot, TableSlot.cast_index, TableSlot.setOther, TableSlot.appendRight, TableSlot.ofIndex]

private theorem physical_length
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    witness.tables.length = (beforeChecks image source others resources).length + 2 := by
  rw [← witness.same_length, tables_eq]
  simp only [List.length_set, List.length_append, FinalMemoryChecks.checkTables,
    List.length_cons, List.length_nil]

/-- The existing final rows and appended checks are exactly the five-table proof view. -/
theorem boundaryTables_eq
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels)) :
    boundaryTables witness = (witness.tables.drop 3).take 3 ++
      witness.tables.drop (beforeChecks image source others resources).length := by
  have length := physical_length witness
  have lower : 6 ≤ (beforeChecks image source others resources).length := by rw [prefix_length]; omega
  have finals : (witness.tables.drop 3).take 3 =
      [(finalSlot ⟨0, by decide⟩).table witness, (finalSlot ⟨1, by decide⟩).table witness,
       (finalSlot ⟨2, by decide⟩).table witness] := by
    apply List.ext_getElem
    · simp only [List.length_take, List.length_drop, List.length_cons, List.length_nil]
      omega
    · intro index left right
      have bound : index < 3 := by simpa using right
      interval_cases index <;> simp only [List.getElem_take, List.getElem_drop]
      all_goals rfl
  have checks : witness.tables.drop (beforeChecks image source others resources).length =
      [(checkSlot ⟨0, by decide⟩).table witness, (checkSlot ⟨1, by decide⟩).table witness] := by
    apply List.ext_getElem
    · simp only [List.length_drop, List.length_cons, List.length_nil]
      omega
    · intro index left right
      have bound : index < 2 := by simpa using right
      interval_cases index <;>
        simp only [List.getElem_drop, List.getElem_cons_zero, List.getElem_cons_succ,
          TableSlot.table, checkSlot_position, Nat.add_zero]
  rw [finals, checks]
  rfl

private theorem initial_silent
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    (witness.tables.take 3).flatMap (·.interactionsWith channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_take, witness.tables_map_component, tables_eq,
    List.take_set_of_le (by decide : 3 ≤ 4), List.take_set_of_le (by decide : 3 ≤ 3),
    List.take_set_of_le (by decide : 3 ≤ 57), List.take_append_of_le_length (by rw [prefix_length]; omega)] at component
  exact table.interactionsWith_nil_of_channel_not_mem
    (beforeChecks_private interface channel privateChannel _ (List.mem_of_mem_take component))

private theorem middle_silent
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    ((witness.tables.take (beforeChecks image source others resources).length).drop 6).flatMap
      (·.interactionsWith channel) = [] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro table member
  have component := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
  rw [List.map_drop, List.map_take, witness.tables_map_component, tables_eq] at component
  simp only [List.take_set, List.take_append_length] at component
  rw [List.drop_set_of_lt (by decide : 4 < 6), List.drop_set_of_lt (by decide : 3 < 6),
    List.drop_set, if_neg (by decide : ¬57 < 6)] at component
  apply table.interactionsWith_nil_of_channel_not_mem
  rcases List.mem_or_eq_of_mem_set component with old | same
  · exact beforeChecks_private interface channel privateChannel _ (List.mem_of_mem_drop old)
  · rw [same]
    exact padding_private channel privateChannel

/-- Dropping unrelated physical rows changes none of the three private receipt ledgers. -/
theorem boundaryTables_interactions
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    witness.tables.flatMap (·.interactionsWith channel) =
      (boundaryTables witness).flatMap (·.interactionsWith channel) := by
  let count := (beforeChecks image source others resources).length
  have lower : 6 ≤ count := by dsimp only [count]; rw [prefix_length]; omega
  have prefixSplit : witness.tables.take count =
      witness.tables.take 3 ++ (witness.tables.drop 3).take 3 ++ (witness.tables.take count).drop 6 := by
    calc
      witness.tables.take count = (witness.tables.take count).take 6 ++ (witness.tables.take count).drop 6 :=
        (List.take_append_drop 6 _).symm
      _ = witness.tables.take 6 ++ (witness.tables.take count).drop 6 := by
        rw [List.take_take, Nat.min_eq_left lower]
      _ = _ := by rw [show 6 = 3 + 3 from rfl, List.take_add]
  calc
    witness.tables.flatMap (·.interactionsWith channel) =
        (witness.tables.take count ++ witness.tables.drop count).flatMap (·.interactionsWith channel) :=
      congrArg (List.flatMap (·.interactionsWith channel)) (List.take_append_drop count witness.tables).symm
    _ = _ := by
      rw [List.flatMap_append, prefixSplit, List.flatMap_append, List.flatMap_append,
        initial_silent witness interface channel privateChannel,
        middle_silent witness interface channel privateChannel,
        List.nil_append, List.append_nil, boundaryTables_eq, List.flatMap_append]

private theorem verifier_values
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (channel : RawChannel (ZMod p)) (privateChannel : channel ∈ privateChannels (p := p)) :
    witness.verifierTable.interactionsWith channel =
      if channel = FinalMemoryChange.channel.toRaw then
        (source.sail.memorySnapshot.changes target).map
          (fun loc => FinalMemoryChange.channel.pulledValue (FinalMemoryChange.encode loc)) else [] := by
  refine ((FinalMemoryChangeBoundary.closed source.sail.memorySnapshot target).installed_verifier_interactions
    witness channel).trans ?_
  have silent : (receiptWitness witness).verifierTable.interactionsWith channel = [] := by
    apply Table.interactionsWith_nil_of_channel_not_mem
    exact base_verifier_private (image := image) (source := source) (target := target)
      (final := final) (bankFinal := bankFinal) (others := others) (resources := resources)
      (channels := channels) channel privateChannel
  change (receiptWitness witness).verifierTable.interactionsWith channel ++ _ = _
  rw [silent, List.nil_append, ClosedVerifier.singleton_interactions]
  simp only [FinalMemoryChangeBoundary.closed, FinalMemoryChangeBoundary.circuit,
    FinalMemoryChangeBoundary.values, List.map_map, Function.comp_def]

/-- The boundary view has exactly the full assembly's receipt ledgers, including count bounds. -/
theorem boundaryWitness_interactions
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) :
    (boundaryWitness witness).interactionsWith channel = witness.interactionsWith channel := by
  simp only [EnsembleWitness.interactionsWith, EnsembleWitness.allTables, List.flatMap_cons,
    boundaryWitness_tables]
  rw [boundaryTables_interactions witness interface channel privateChannel,
    verifier_values witness channel privateChannel, FinalMemoryChecks.verifier_values]
  simp only [privateChannels, List.mem_cons, List.not_mem_nil, or_false] at privateChannel
  rcases privateChannel with rfl | rfl | rfl <;>
    simp [FinalMemoryValue.channel, FinalMemoryChange.channel, OrderedBoundary.channel,
      OrderedFinalProvider.channelName, Channel.toRaw]

/-- Receipt balance transfers independently of Byte and Memory balance in the smaller view. -/
theorem boundaryWitness_balancedChannel
    (witness : EnsembleWitness (ensemble image source target final bankFinal others resources channels))
    (interface : PrivateInterface others resources) (channel : RawChannel (ZMod p))
    (privateChannel : channel ∈ privateChannels (p := p)) (balanced : witness.BalancedChannel channel) :
    (boundaryWitness witness).BalancedChannel channel := by
  change BalancedInteractions ((boundaryWitness witness).interactionsWith channel)
  rw [boundaryWitness_interactions witness interface channel privateChannel]
  exact balanced

end SP1Clean.Soundness.HostFinalMemory
