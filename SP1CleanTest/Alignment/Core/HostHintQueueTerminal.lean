import SP1Clean.Native.Operations.HostHintQueueTerminal
import SP1CleanTest.Core.EnsembleExport
import SP1Clean.Semantics.ReleasePolicy
import ToClean.Circuit.SubcircuitProjection

/-! # Physical generation and rejection at the private hint terminal -/

namespace SP1CleanTest.HostHintQueueTerminal

open Circuit Air.Flat SP1Clean SP1Clean.HostHintQueue SP1Clean.HostHintQueueTerminal

private abbrev Fp := ZMod SP1Prime

private def endpoint : State Fp := State.encode (2 ^ 48) 2 3

private def verifier : Verifier.Program Fp State where
  Spec _ _ := True
  soundness := by intros; trivial
  main previous := Verifier.ofInteractions
    [(stateChannel.pushed previous).toRaw, (stateChannel.pulled (const endpoint)).toRaw] (by
      intro interaction member env
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;>
        simp [AbstractInteraction.Requirements, ChannelInteraction.toRaw, stateChannel, Channel.toRaw, circuit_norm])

private def ensemble : Ensemble Fp State where
  tables := [component endpoint]
  unique_names := by simp
  channels := [stateChannel.toRaw]
  unique_channel_names := by simp
  verifier := verifier
  tables_channels := by
    intro table member
    obtain rfl := List.mem_singleton.mp member
    change [stateChannel.toRaw, stateChannel.toRaw] ⊆ _
    simp
  verifier_channels := by
    intro channel member
    rw [Verifier.Program.mem_channels_iff, Operations.channels] at member
    change channel ∈ verifier.circuitOperations.interactions.map (·.channel) at member
    simp only [Verifier.Program.circuitOperations, Verifier.Program.operations, verifier,
      Verifier.ofInteractions_interactions, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact List.mem_singleton.mpr rfl
  ProverInput := fieldPair
  hintTables := [⟨tableName, 2, 0, 1⟩]

private def description : EnsembleCheck ensemble where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    intro table member
    obtain rfl := List.mem_singleton.mp member
    simp [component, Component.lookups_eq, Component.rowOperations, circuit, main,
      Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.ToBits.main, Gadgets.Equality.main, circuit_norm]

private def accepts (message : State Fp) (high low : Fp) : Bool := Id.run do
  match WitnessGeneration.generate ensemble 8 message (high, low) with
  | .error _ => return false
  | .ok witness => return (witness.tables.map (·.length) == [1]) && description.checkWitness witness

theorem accepts_private_timestamp :
    accepts (State.encode 0 2 3) 0 0 = true ∧
    accepts (State.encode (2 ^ 24 + 83) 2 3) 1 83 = true ∧
    accepts (State.encode (2 ^ 48 - 1) 2 3) (2 ^ 24 - 1) (2 ^ 24 - 1) = true := by native_decide

theorem rejects_wrong_timestamp_and_pointers :
    accepts (State.encode 83 2 3) 0 82 = false ∧
    accepts (State.encode 83 1 3) 0 83 = false ∧
    accepts (State.encode 83 2 4) 0 83 = false ∧
    accepts endpoint (2 ^ 24) 0 = false := by native_decide

theorem rust_export : (Backends.Plonky3.Print.ensembleToRust (SP1CleanTest.Core.ComponentExport.fixture ensemble) 8).isOk =
    true := by native_decide

end SP1CleanTest.HostHintQueueTerminal
