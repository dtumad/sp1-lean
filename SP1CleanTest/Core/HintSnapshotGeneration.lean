import SP1Clean.Proofs.Completeness.HintSnapshotTables
import SP1Clean.Native.Operations.HintQueueSource
import SP1Clean.Native.Operations.HintQueueWordSource
import ToClean.Circuit.VerifierInteractions
import Clean.Air.WitnessGeneration
import SP1CleanTest.Core.ComponentExport

/-! # Executing the outgoing queue reader and its two immutable providers

Clean schedules the genuine source, word reader and seal from their own generation modes.
The source snapshot can contain discarded nodes that no longer occur in the public target.
-/

namespace SP1CleanTest.Core.HintSnapshotGeneration
open Circuit Air.Flat SP1Clean Semantics Semantics.HintQueue HostHintQueue HostHintSnapshot

private abbrev F := ZMod SP1Prime

private def verifier (hints : List Bytes) : Verifier.Program F State where
  Spec _ _ := True
  soundness := by intros; trivial
  main actual := Verifier.ofInteractions
    [(stateChannel.pushed actual).toRaw, (stateChannel.pulled (const (HostHintQueueBoundary.initial hints))).toRaw] (by
      intro entry member env
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [AbstractInteraction.Requirements, ChannelInteraction.toRaw, stateChannel, Channel.toRaw, circuit_norm])

/-- Two independent production inventories supply the immutable source records used in this fixture. -/
private def ensemble (source target : List Bytes) : Ensemble F State where
  tables := [HostHintQueue.source source, HostHintQueue.sourceWord source, component target, Seal.component target]
  unique_names := of_decide_eq_true rfl
  channels := [nodeChannel.toRaw, wordChannel.toRaw, channel.toRaw, stateChannel.toRaw]
  unique_channel_names := by decide
  verifier := verifier target
  tables_channels := by
    intro table member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · change [nodeChannel.toRaw] ⊆ _
      simp
    · change [wordChannel.toRaw] ⊆ _
      simp
    · change [channel.toRaw, nodeChannel.toRaw, wordChannel.toRaw, channel.toRaw, nodeChannel.toRaw, wordChannel.toRaw] ⊆ _
      simp
    · change [stateChannel.toRaw, channel.toRaw, stateChannel.toRaw, channel.toRaw] ⊆ _
      simp
  verifier_channels := by
    intro ch member
    rw [Verifier.Program.mem_channels_iff, Operations.channels] at member
    change ch ∈ (verifier target).circuitOperations.interactions.map (·.channel) at member
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, verifier,
      Verifier.ofInteractions_interactions, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
  ProverInput := ProvablePair (ProvableVector Links (inventory (p := SP1Prime) target).height) State
  hintTables := [⟨tableName, size Links, 0, (inventory (p := SP1Prime) target).height⟩,
    ⟨Seal.name, size State, (inventory (p := SP1Prime) target).height * size Links, 1⟩]

private def accepts (source target : List Bytes) (head actualHead : ℕ) : Bool := Id.run do
  let physical := ensemble source target
  let rows := (inputsFor (p := SP1Prime) (ofList source).1 head target).toArray
  let links := Vector.ofFn (fun i : Fin (inventory (p := SP1Prime) target).height => (rows[i.val]?.map (·.2.1)).getD 0)
  let state := State.encode (p := SP1Prime) 128 actualHead source.length
  match WitnessGeneration.generate physical (8 * (source.length + wordRows source + wordRows target + 2))
      state (links, state) with
  | .error _ => return false
  | .ok w => return WitnessGeneration.constraintsHold w && WitnessGeneration.channelsBalanced w

private def source : List Bytes := [[0], [1,2,3,4,5,6,7,8], [], [9]]

example : accepts [] [] 0 0 ∧ accepts source source 4 4 ∧ accepts source source.tail 3 3 ∧
    accepts source [] 0 0 ∧ accepts source source.tail 3 4 = false ∧
    accepts source [[1,2,3,4,5,6,7,9], [], [9]] 3 3 = false := by native_decide

/-- Lower the complete four-table queue fixture using Clean's production AIR and scheduler. -/
def rustExport : Except String String :=
  Backends.Plonky3.Print.ensembleToRust (ComponentExport.fixture (ensemble source source.tail)) 128

end SP1CleanTest.Core.HintSnapshotGeneration
