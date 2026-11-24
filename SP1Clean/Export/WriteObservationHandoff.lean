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
    (unused : ch.name ∉ (tables source.host target.host).flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    w.interactionsWith ch = (supervisor w).interactionsWith ch := by
  apply ((appended image source target final).ledger_of_silent w ch ?_).trans (project_ledger _ ch original).symm
  intro c declared used
  exact unused (List.mem_flatMap.mpr ⟨c, declared, List.mem_map_of_mem used⟩)

/-- The HINT_READ transfer cursor and its original node-word provider retain all signed
occurrences in the supervisor used by chronological handoff decoding. -/
theorem hint_ledger (w : EnsembleWitness (preprocessing image source target final)) (ch : RawChannel F)
    (which : ch = HintReadWordChip.stateChannel.toRaw ∨ ch = HostHintQueue.wordChannel.toRaw) :
    w.interactionsWith ch = (supervisor w).interactionsWith ch := by
  apply unchanged_ledger
  · rcases which with rfl | rfl <;> intro eq <;>
      exact Bool.noConfusion (congrArg (fun c => c.name == "sp1.native.write_readback") eq)
  · rcases which with rfl | rfl <;> exact of_decide_eq_true rfl

private theorem silent {cs : List (Component F)} {ch : RawChannel F}
    (absent : ch.name ∉ cs.flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
    ∀ c ∈ cs, ch ∉ c.circuit.channels :=
  fun c member used => absent (List.mem_flatMap.mpr ⟨c, member, List.mem_map_of_mem used⟩)

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
