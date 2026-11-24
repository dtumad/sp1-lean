import ToClean.Air.AppendedAuthentication
import SP1Clean.Export.WriteObservationSources

/-! # Exact physical handoff ledgers for chronological host-call decoding -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe WriteSourceRegistry

private abbrev F := ZMod SP1Prime

variable (image : ProgramImage) (source target : ExecutionSnapshot) (final : HostHintQueue.State F)

/-- The eighth handler receives WRITE calls at this physical packet slot. -/
def packetSlot : TableSlot (preprocessing image source target final).tables WritePacket.component :=
  slot image source target final 2

attribute [local irreducible] base withSources preprocessing

variable {image source target final}

/-- A channel unused by the observer suffix retains its exact original signed ledger. -/
theorem unchanged_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (original : ch ≠ readbackChannel.toRaw)
    (unused : ch.name ∉ (tables source target).flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    w.interactionsWith ch = (supervisor w).interactionsWith ch := by
  apply ((appended image source target final).ledger_of_silent w ch ?_).trans (project_ledger _ ch original).symm
  intro c declared used
  exact unused (List.mem_flatMap.mpr ⟨c, declared, List.mem_map_of_mem used⟩)

/-- The HINT_READ transfer cursor retains the original chronological handoff ledger. -/
theorem hintCursor_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    w.interactionsWith HintReadWordChip.stateChannel.toRaw =
      (supervisor w).interactionsWith HintReadWordChip.stateChannel.toRaw :=
  unchanged_ledger w _ (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
    (of_decide_eq_true rfl)

private theorem silent {cs : List (Component F)} {ch : RawChannel F}
    (absent : ch.name ∉ cs.flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    ∀ c ∈ cs, ch ∉ c.circuit.channels :=
  fun c member used => absent (List.mem_flatMap.mpr ⟨c, member, List.mem_map_of_mem used⟩)

private theorem flatMap_selected {α β : Type} (xs : List α) (used : α → Bool) (ledger : α → List β)
    (absent : ∀ x ∈ xs, used x = false → ledger x = []) :
    xs.flatMap ledger = (xs.filter used).flatMap ledger := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have tail := ih (fun y member => absent y (List.mem_cons_of_mem x member))
    cases enabled : used x <;> simp [enabled, tail, absent x List.mem_cons_self]

/-- Physical suffix slots declaring a channel, in installation order. -/
def selectedSlots (source target : ExecutionSnapshot) (ch : RawChannel F) : List (Fin 19) :=
  (List.finRange 19).filter fun i => ((tables source target)[i.val].circuit.channels.map RawChannel.name).contains ch.name

private theorem selected_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (distinct : ch ≠ readbackChannel.toRaw) :
    w.interactionsWith ch = (supervisor w).interactionsWith ch ++
      (selectedSlots source target ch).flatMap (fun i => ((slot image source target final i).table w).interactionsWith ch) := by
  let install := appended image source target final
  let physical := fun i => (slot image source target final i).table w
  have size := congrArg List.length (install.suffix_components w)
  rw [List.length_map] at size
  have rows : w.tables.drop (withSources image source target final).tables.length = (List.finRange 19).map physical := by
    apply List.ext_getElem
    · rw [size, List.length_map, List.length_finRange]; rfl
    · intro i hi hj
      simp only [List.getElem_drop, List.getElem_map, List.getElem_finRange]
      rfl
  rw [install.ledger, rows, List.flatMap_map]
  apply congrArg₂ List.append (project_ledger _ ch distinct).symm
  apply flatMap_selected
  intro i _ missing
  apply Table.interactionsWith_nil_of_channel_not_mem
  rw [(slot image source target final i).table_component w]
  intro present
  exact Bool.noConfusion ((List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) present)).symm.trans missing)

/-- A fresh protocol is funded entirely inside its own declared physical suffix slots.
The equality includes disabled interactions, repeated messages and both directions. -/
theorem fresh_slots_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (registered : ch ∈ channels) (distinct : ch ≠ readbackChannel.toRaw) :
    w.interactionsWith ch = (selectedSlots source target ch).flatMap
      (fun i => ((slot image source target final i).table w).interactionsWith ch) := by
  rw [selected_ledger w ch distinct]
  have projected := project_ledger ((appended image source target final).project w) ch distinct
  change (supervisor w).interactionsWith ch = _ at projected
  rw [projected, EnsembleWitness.interactionsWith_nil_of_not_registered _ _ (protocol_fresh image source target final ch registered),
    List.nil_append]

/-- The immutable metadata ledger retains every original supervisor occurrence, both the
fixed outgoing snapshot's read sites and the fresh node table's counted publications. -/
theorem hintNode_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (HostHintQueue.nodeChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = (supervisor w).interactionsWith ch ++
      (((slot image source target final 10).table w).interactionsWith ch ++
       ((slot image source target final 16).table w).interactionsWith ch) := by
  let ch := (HostHintQueue.nodeChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [10,16] := rfl
  simpa only [support, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    selected_ledger w ch (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- Immutable word reads share one physical ledger with both the incoming word inventory
and the actual words published by the dynamically allocating table. Padding is retained. -/
theorem hintWord_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (HostHintQueue.wordChannel (p := SP1Prime)).toRaw
    w.interactionsWith ch = (supervisor w).interactionsWith ch ++
      (((slot image source target final 10).table w).interactionsWith ch ++
       ((slot image source target final 18).table w).interactionsWith ch) := by
  let ch := (HostHintQueue.wordChannel (p := SP1Prime)).toRaw
  have support : selectedSlots source target ch = [10,18] := rfl
  simpa only [support, List.flatMap_cons, List.flatMap_nil, List.append_nil] using
    selected_ledger w ch (fun eq => Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))

/-- HostCall contains the genuine supervisor's ordered occurrences followed by every
signed packet-row pull, including disabled padding. -/
theorem hostCall_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    w.interactionsWith HostCallChip.channel.toRaw = (supervisor w).interactionsWith HostCallChip.channel.toRaw ++
      ((packetSlot image source target final).table w).interactionsWith HostCallChip.channel.toRaw := by
  let install := appended image source target final
  let ch := (HostCallChip.channel (p := SP1Prime)).toRaw
  have split := install.ledger_at w ch 2 (packetSlot image source target final) rfl
    (silent (of_decide_eq_true rfl)) (silent (of_decide_eq_true rfl))
  have prior := project_ledger (install.project w) ch (fun eq =>
    Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq))
  exact split.trans (congrArg (fun l => l ++ _) prior.symm)

end SP1Clean.Export.WriteObservationAssembly
