import SP1Clean.Export.WriteObservationSources
import SP1Clean.Soundness.HintSnapshotDecode
import ToClean.Air.AppendedAuthentication

/-! # The ordered outgoing queue walk in the installed native verifier

The word reader and the singleton seal own the complete word-walk ledger. Raw LogUp
acceptance therefore connects each public word, in physical order, to the actual
outgoing head recorded by the seal and ultimately to the null pointer.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics Soundness HostHintSnapshot WriteSourceRegistry

private abbrev F := ZMod SP1Prime
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

attribute [local irreducible] base withSources preprocessing

private theorem walk_channel : (HostHintSnapshot.channel (p := SP1Prime)).toRaw ∈ channels := by
  apply List.mem_of_getElem? (i := 10)
  rfl

/-- Every word-walk occurrence belongs to exactly these two physical slots. -/
theorem hint_walk_ledger (w : EnsembleWitness (preprocessing image source target final)) :
    let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
    w.interactionsWith ch = ((slot image source target final 10).table w).interactionsWith ch ++
      ((slot image source target final 11).table w).interactionsWith ch := by
  let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
  let prior := withSources image source target final
  let install := appended image source target final
  let suffix := w.tables.drop prior.tables.length
  let reader := slot image source target final 10
  let terminal := slot image source target final 11
  have silent {cs : List (Component F)} (names : ch.name ∉ cs.flatMap (fun c => c.circuit.channels.map RawChannel.name)) :
      ∀ c ∈ cs, ch ∉ c.circuit.channels :=
    fun c member used => names (List.mem_flatMap.mpr ⟨c,member,List.mem_map_of_mem used⟩)
  have eq := install.ledger_window w ch 10 2 (silent (of_decide_eq_true rfl)) (silent (of_decide_eq_true rfl))
  rw [EnsembleWitness.interactionsWith_nil_of_not_registered _ _ (protocol_fresh image source target final _ walk_channel),
    List.nil_append] at eq
  have registered : suffix.map (·.component) = tables source target := install.suffix_components w
  have length : 11 < suffix.length := by
    have size := congrArg List.length registered
    rw [List.length_map] at size
    rw [size]
    simp [tables]
  have readerRow : suffix[10]'(by omega) = reader.table w := by
    simp only [suffix, List.getElem_drop]
    rfl
  have sealRow : suffix[11]'(by omega) = terminal.table w := by
    simp only [suffix, List.getElem_drop]
    rfl
  change w.interactionsWith ch = (reader.table w).interactionsWith ch ++ (terminal.table w).interactionsWith ch
  rw [eq]
  change ((suffix.drop 10).take 2).flatMap _ = _
  rw [List.drop_eq_getElem_cons (by omega : 10 < suffix.length), List.drop_eq_getElem_cons (by omega : 11 < suffix.length),
    readerRow, sealRow]
  simp

/-- For a raw accepted native witness, all target words lie on the connected walk from the
private outgoing head to null, in exactly the public snapshot's order. -/
theorem native_hint_walk (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let reader := (slot image source target endQueue 10).table seen
    let terminal := slot image source target endQueue 11
    let state := Seal.physicalState target.host.io.hints (terminal.table seen) (terminal.table_component seen)
    Walk.IsWalk (physicalEdge reader) (endpoint 0 state.head) (endpoint (wordRows target.host.io.hints) 0)
      ((List.finRange reader.table.length).take (wordRows target.host.io.hints)) := by
  let seen := observed w
  let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
  let reader := slot image source target endQueue 10
  let terminal := slot image source target endQueue 11
  let ch := (HostHintSnapshot.channel (p := SP1Prime)).toRaw
  have paid := observed_balance w fit raw ch (protocol_installed image source target endQueue _ walk_channel)
    (of_decide_eq_true rfl)
  change BalancedInteractions (seen.interactionsWith ch) at paid
  rw [hint_walk_ledger seen] at paid
  have reordered := BalancedInteractions.of_perm paid (List.perm_append_comm ..)
  have ends := Seal.physical_walk_ledger target.host.io.hints (terminal.table seen) (terminal.table_component seen)
  rw [ends] at reordered
  exact physical_walk target.host.io.hints (reader.table seen) (reader.table_component seen)
    (reader.table_constraints seen ((observed_constraints w).mp checked)) _ reordered

/-- Once the whole witness's immutable lookup channels identify a common persistent store,
raw native acceptance forces that store to represent the complete public target queue. -/
theorem outgoing_queue_of_immutable_reads (store : HintQueue.Store)
    (w : EnsembleWitness (native image source target)) (checked : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp)
    (nodes : ∀ r, HostHintQueue.nodeChannel.pulledValue r ∈ w.interactionsWith HostHintQueue.nodeChannel.toRaw →
      r.Valid ∧ r.Binds store)
    (words : ∀ r, HostHintQueue.wordChannel.pulledValue r ∈ w.interactionsWith HostHintQueue.wordChannel.toRaw →
      r.Binds store) :
    let seen := observed w
    let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) target.host.io.hints
    let terminal := slot image source target endQueue 11
    let state := Seal.physicalState target.host.io.hints (terminal.table seen) (terminal.table_component seen)
    HintQueue.Represents store (Address.toNat state.head) target.host.io.hints := by
  let hints := target.host.io.hints
  let seen := observed w
  let endQueue := SP1Clean.HostHintQueueBoundary.initial (p := SP1Prime) hints
  let reader := slot image source target endQueue 10
  let table := reader.table seen
  let installed : TableSlot (native image source target).tables (HostHintSnapshot.component (p := SP1Prime) hints) := reader
  have carries (ch : RawChannel F) : table.interactionsWith ch ⊆ w.interactionsWith ch :=
    installed.table_interactions_subset w ch
  have visible (i : Fin table.table.length) (_ : i.val < wordRows hints) : BoundReads store (physicalInput table i) := by
    have requirements := physical_lookups hints table (reader.table_component seen) i
    constructor
    · intro first
      exact nodes _ (carries _ (requirements.1 first))
    · intro active
      exact words _ (carries _ (requirements.2 active))
  obtain ⟨tails, chain⟩ := reads_snapshot_of_walk store hints table (reader.table_component seen)
    (reader.table_constraints seen ((observed_constraints w).mp checked)) _ (native_hint_walk w checked fit raw) visible
  exact chain.represents

end SP1Clean.Export.WriteObservationAssembly
