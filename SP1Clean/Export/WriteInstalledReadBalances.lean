import SP1Clean.Export.WriteObservationBuild
import SP1Clean.Export.WriteObservationReads

/-! # Exact read-protocol balances after canonical installation

The read-back supplier, probes, packet, span and word tables are the only observer components
using these five protocols. Their raw balances therefore hold in the fully registered ensemble,
including all later host, queue and output components.
-/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteProbe WriteSourceRegistry

private abbrev F := ZMod SP1Prime

/-- Internal channels connecting the first five WRITE observer tables to their original publishers. -/
def readProtocols : List (RawChannel F) :=
  [readbackChannel.toRaw, versionChannel.toRaw, readChannel.toRaw, WritePacket.channel.toRaw, WriteBuffer.channel.toRaw]

private def uses (ch : RawChannel F) (t : Table F) : Bool := (t.component.circuit.channels.map RawChannel.name).contains ch.name

private theorem active_ledger (ch : RawChannel F) (xs : List (Table F)) :
    xs.flatMap (·.interactionsWith ch) = (xs.filter (uses ch)).flatMap (·.interactionsWith ch) := by
  induction xs with
  | nil => rfl
  | cons t rest ih =>
    cases contains : uses ch t
    · have quiet : ch ∉ t.component.circuit.channels := by
        intro member
        have actual : uses ch t = true := List.contains_iff_mem.mpr (List.mem_map_of_mem member)
        exact Bool.noConfusion (actual.symm.trans contains)
      rw [List.flatMap_cons, t.interactionsWith_nil_of_channel_not_mem quiet, List.nil_append, List.filter_cons, contains]
      exact ih
    · simp only [List.filter_cons, contains, List.flatMap_cons, ↓reduceIte, ih]

private theorem filter_registry (ch : RawChannel F) (xs : List (Table F)) :
    xs.filter (uses ch) = ((xs.zip (xs.map (·.component))).filter fun pair =>
      (pair.2.circuit.channels.map RawChannel.name).contains ch.name).map Prod.fst := by
  induction xs with
  | nil => rfl
  | cons t rest ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.filter_cons, uses]
    split <;> rename_i guard <;> simp only [guard, Bool.false_eq_true, ↓reduceIte, List.map_cons, ← ih]

private theorem silent_tail {source target : ExecutionSnapshot} (tail : List (Table F))
    (registry : tail.map (·.component) = (tables source target).drop 5) (ch : RawChannel F) (which : ch ∈ readProtocols) :
    tail.flatMap (·.interactionsWith ch) = [] := by
  have absent : ch.name ∉ ((tables source target).drop 5).flatMap (fun c => c.circuit.channels.map RawChannel.name) := by
    simp only [readProtocols, List.mem_cons, List.not_mem_nil, or_false] at which
    rcases which with rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_true rfl
  apply List.flatMap_eq_nil_iff.mpr
  intro t mem
  apply t.interactionsWith_nil_of_channel_not_mem
  exact fun here => absent (List.mem_flatMap.mpr ⟨t.component, registry ▸ List.mem_map_of_mem mem, List.mem_map_of_mem here⟩)

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

/-- Five exact raw balances on the generated tables close the corresponding channels of the
canonical supervisor-plus-observer ensemble, for every registered later suffix. -/
theorem compiled_read_balances (w : EnsembleWitness (base image source target final)) (supply probe packet span word : Table F)
    (physical : [supply,probe,packet,span,word].map (·.component) = (tables source target).take 5)
    (back : LogUpBalanced ((installSources w).interactionsWith readbackChannel.toRaw ++ supply.interactionsWith readbackChannel.toRaw))
    (version : LogUpBalanced (supply.interactionsWith versionChannel.toRaw ++ probe.interactionsWith versionChannel.toRaw))
    (read : LogUpBalanced (probe.interactionsWith readChannel.toRaw ++ packet.interactionsWith readChannel.toRaw ++ word.interactionsWith readChannel.toRaw))
    (header : LogUpBalanced (packet.interactionsWith WritePacket.channel.toRaw ++ span.interactionsWith WritePacket.channel.toRaw))
    (buffer : LogUpBalanced (span.interactionsWith WriteBuffer.channel.toRaw ++ word.interactionsWith WriteBuffer.channel.toRaw))
    (tail : List (Table F)) (registry : tail.map (·.component) = (tables source target).drop 5)
    (ch : RawChannel F) (which : ch ∈ readProtocols) :
    let block := [supply,probe,packet,span,word]
    let full := build w (block ++ tail) (by rw [List.map_append, physical, registry, List.take_append_drop])
    LogUpBalanced (full.interactionsWith ch) := by
  let block := [supply,probe,packet,span,word]
  have select (ch : RawChannel F) : block.filter (uses ch) =
      ((block.zip ((tables source target).take 5)).filter fun pair =>
        (pair.2.circuit.channels.map RawChannel.name).contains ch.name).map Prod.fst := by
    rw [filter_registry, ← physical]
  dsimp only
  rw [build_ledger, List.flatMap_append, silent_tail tail registry ch which, List.append_nil, active_ledger]
  have prior (c : RawChannel F) (mem : c ∈ channels) : (installSources w).interactionsWith c = [] :=
    (installSources w).interactionsWith_nil_of_not_registered c (protocol_fresh image source target final c mem)
  simp only [readProtocols,List.mem_cons,List.not_mem_nil,or_false] at which
  rcases which with rfl | rfl | rfl | rfl | rfl
  · have slots : block.filter (uses readbackChannel.toRaw) = [supply] := by
      rw [select]; rfl
    simpa only [show [supply,probe,packet,span,word].filter (uses readbackChannel.toRaw) = _ from slots,
      List.flatMap_singleton] using back
  all_goals rw [prior _ (by simp [channels])]
  all_goals rw [List.nil_append]
  · have slots : block.filter (uses versionChannel.toRaw) = [supply,probe] := by
      rw [select]; rfl
    rw [slots]; simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using version
  · have slots : block.filter (uses readChannel.toRaw) = [probe,packet,word] := by
      rw [select]; rfl
    rw [slots]; simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil,List.append_assoc] using read
  · have slots : block.filter (uses WritePacket.channel.toRaw) = [packet,span] := by
      rw [select]; rfl
    rw [slots]; simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using header
  · have slots : block.filter (uses WriteBuffer.channel.toRaw) = [span,word] := by
      rw [select]; rfl
    rw [slots]; simpa only [List.flatMap_cons,List.flatMap_nil,List.append_nil] using buffer

private theorem read_guarantees_setData {source target : ExecutionSnapshot} {t : Table F}
    (physical : t.component ∈ (tables source target).take 5) {i : Interaction F} (used : i ∈ t.interactions)
    {old fresh : ProverData F} (original : i.Guarantees old) : i.Guarantees fresh := by
  have channel := t.channel_mem_channels_of_mem_interactions i used
  have seen : i.channel ∈ ((tables source target).take 5).flatMap (·.circuit.channels) :=
    List.mem_flatMap.mpr ⟨t.component, physical, channel⟩
  have transfer : ∀ c ∈ ((tables source target).take 5).flatMap (·.circuit.channels),
      ∀ (interaction : Interaction F), interaction.channel = c → interaction.Guarantees old → interaction.Guarantees fresh := by
    repeat' refine List.forall_mem_cons.mpr ⟨?_, ?_⟩
    all_goals first
      | exact fun _ mem => False.elim (List.not_mem_nil mem)
      | intro ⟨ch, _, _, _, _⟩ same valid
        change ch = _ at same
        subst ch
        exact valid
  exact transfer i.channel seen i rfl original

/-- The five registered tables retain every constraint and guarantee at the canonical data of
the complete installed ensemble, independently of the later tables' validity. -/
theorem compiled_read_constraints (w : EnsembleWitness (base image source target final)) (block tail : List (Table F))
    (physical : block.map (·.component) = (tables source target).take 5)
    (valid : ∀ t ∈ block, t.Constraints ∧ t.Guarantees)
    (registered : tail.map (·.component) = (tables source target).drop 5) :
    let full := build w (block ++ tail) (by rw [List.map_append, physical, registered, List.take_append_drop])
    ∀ t ∈ (full.tables.drop (installSources w).tables.length).take block.length, t.Constraints ∧ t.Guarantees := by
  intro full t actual
  let pairs (q : Table F) := (q.component, q.table)
  have collected := List.mem_map_of_mem (f := pairs) actual
  have equiv : ((full.tables.drop (installSources w).tables.length).take block.length).map pairs = block.map pairs := by
    rw [List.map_take, List.map_drop]
    dsimp only [full, build, Ensemble.AppendedTables.extend]
    rw [EnsembleWitness.ofTables_tables]
    change (((withDerivedData _ _ _).map (fun q : Table F => (q.component, q.table))).drop _).take _ = _
    rw [withDerivedData_map, List.map_append, ← List.length_map pairs (as := (installSources w).tables), List.drop_left,
      List.map_append, ← List.length_map pairs (as := block), List.take_left]
  rw [equiv] at collected
  obtain ⟨before, member, same⟩ := List.mem_map.mp collected
  obtain ⟨component, cells⟩ := Prod.mk.inj same
  have own : t.component ∈ (tables source target).take 5 := physical ▸ component ▸ List.mem_map_of_mem member
  have free := suffix_lookupFree source target t.component (List.mem_of_mem_take own)
  obtain ⟨checked, guaranteed⟩ := valid before member
  refine ⟨?_, t.guarantees_iff_forall.mpr ?_⟩
  · intro row inside
    have checkedRow := checked row (cells ▸ inside)
    rw [component] at checkedRow
    exact t.component.constraintsHold_setData free checkedRow
  · intro i used
    apply read_guarantees_setData own used (old := before.data)
    apply before.guarantees_iff_forall.mp guaranteed
    have sameInteractions : t.interactions = before.interactions := by
      simp only [Table.interactions, Table.environment, ← component, ← cells]
      apply List.flatMap_congr
      exact fun _ _ => Operations.interactionValues_congr rfl
    exact sameInteractions ▸ used

end SP1Clean.Export.WriteObservationAssembly
