import SP1Clean.Export.WriteFundedByteProviders
import ToClean.Air.SelectedFootprint
import ToClean.Air.DemandHeightInterval

/-! # Byte capacity of the original sparse RAM inventory

The three RAM components validate the source snapshot, order its final Memory record
and check the target snapshot. Their actual circuit widths apply to every physical row,
even for a word requested only by a native read-only observer.
-/

namespace SP1Clean.Export.WriteSparseByteCapacity
open Circuit Air.Flat Semantics Soundness Machine TraceGen Channels WriteSourceRegistry WriteProbe.AccessInventory
private abbrev F := ZMod SP1Prime
private abbrev bus := (byteChannel (p := SP1Prime)).toRaw
private def onByte (a : AbstractInteraction F) := a.channel.name == "SP1Byte"

private theorem named_width {image : ProgramImage} {initial final : ExecutionSnapshot} {finish : HostHintQueue.State F}
    (c : Component F) (registered : c ∈ (base image initial final finish).tables) :
    c.channelWidth bus = c.rowOperations.interactions.countP onByte := by
  classical
  let ens := base image initial final finish
  have declared : bus ∈ ens.channels := ens.tables_channels (original .refresh) (List.mem_of_getElem? (original_at image initial final finish .refresh))
    (show bus ∈ (original .refresh : Component F).circuit.channels from List.mem_cons_self)
  rw [Component.channelWidth,Component.interactionsWith_eq,Operations.interactionsWith,List.countP_eq_length_filter]
  apply congrArg List.length
  apply List.filter_congr
  intro a mem
  have ch : a.channel ∈ ens.channels := ens.tables_channels c registered (c.circuit.channels_subset c.rowInputVar c.rowOffset (List.mem_map_of_mem mem))
  rw [Bool.eq_iff_iff,decide_eq_true_iff,onByte,beq_iff_eq]
  exact ⟨fun e => congrArg RawChannel.name e,fun e => List.inj_on_of_nodup_map ens.unique_channel_names ch declared e⟩

private theorem none {I O : TypeMap} [ProvableType I] [ProvableType O] (c : FormalCircuitBase F I O)
    (absent : c.channels.all (fun ch => ch.name != "SP1Byte") = true) (i : Var I F) (n : ℕ) :
    ((c.main i).operations n).interactions.countP onByte = 0 := by
  rw [List.countP_eq_length_filter,List.length_eq_zero_iff,List.filter_eq_nil_iff]
  intro a mem
  have ch := c.channels_subset i n (List.mem_map_of_mem (f := AbstractInteraction.channel) mem)
  simpa [onByte] using List.all_eq_true.mp absent a.channel ch

private theorem guarded (e : Expression F) (xs : List (AbstractInteraction F)) :
    (xs.map (AbstractInteraction.guard e)).countP onByte = xs.countP onByte := by rw [List.countP_map]; rfl

private theorem word (i : Var Word F) (n : ℕ) :
    ((WordRangeCheck.circuit.main i).operations n).interactions.countP onByte = 0 :=
  none WordRangeCheck.circuit.base (by rfl) i n

private theorem add (i : Var AddOperation.Inputs F) (n : ℕ) :
    ((AddOperation.circuit.main i).operations n).interactions.countP onByte = 4 := by
  simp only [AddOperation.circuit,AddOperation.main,circuit_norm]
  rfl

private theorem cmp (i : Var LtOperationUnsigned.Inputs F) (n : ℕ) :
    ((LtOperationUnsigned.circuit.main i).operations n).interactions.countP onByte = 1 := by
  simp only [LtOperationUnsigned.circuit,LtOperationUnsigned.main,U16CompareOperation.circuit,U16CompareOperation.main,
    circuit_norm,FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.main]
  rfl

private theorem address (i : Var AddressOperation.Inputs F) (n : ℕ) :
    ((AddressOperation.circuit.main i).operations n).interactions.countP onByte = 4 := by
  simp only [AddressOperation.circuit,AddressOperation.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    AddrAddOperation.circuit,AddrAddOperation.main,Gadgets.Equality.main]
  rfl

private theorem lookup (m : ByteMemory) (k : String) (apart : k ≠ "SP1Byte") (i : Var Word F) (n : ℕ) :
    ((InitialMemoryLookup.main m (2^48) i k).operations n).interactions.countP onByte = 2 := by
  simp only [InitialMemoryLookup.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    List.countP_append,word,cmp,List.countP_cons]
  simp [onByte,InitialMemoryLookup.membership,StaticTable.channel,apart,circuit_norm]

private theorem readWord (m : ByteMemory) (k : String) (apart : k ≠ "SP1Byte") (i : Var Word F) (n : ℕ) :
    ((InitialMemoryRead.main m i k).operations n).interactions.countP onByte = 44 := by
  simp only [InitialMemoryRead.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions,InitialMemoryLookup.circuitNamed,List.ofFn_succ,List.ofFn_zero,
    List.flatten_cons,List.flatten_nil,List.countP_append,lookup m k apart,add]

private theorem ordered (name : String) (apart : name ≠ "SP1Byte") (i : Var OrderedBoundary.Inputs F) (n : ℕ) :
    (((OrderedBoundary.circuit name).main i).operations n).interactions.countP onByte = 1 := by
  simp only [OrderedBoundary.circuit,OrderedBoundary.main,circuit_norm,
    FormalAssertion.toSubcircuit_interactions,List.countP_append,word,cmp]
  simp [onByte,OrderedBoundary.channel,apart,circuit_norm]

private theorem orderWidth {I : TypeMap} [ProvableType I] (name : String) (apart : name ≠ "SP1Byte")
    (spec : MemoryMsg F → Prop) (provider : GeneralFormalCircuit F I MemoryMsg) [Guarded.Supported provider]
    (binds : ∀ i o d, provider.Spec i o d → spec o) (canonical : ∀ r, spec r → MemoryBoundary.CanonicalSpec r)
    (cost : ℕ) (child : ∀ i n, ((provider.main i).operations n).interactions.countP onByte = cost)
    (i : Var (OrderedMemoryProvider.RowInput I) F) (n : ℕ) :
    (((OrderedMemoryProvider.circuit name spec provider binds canonical).main i).operations n).interactions.countP onByte = cost + 5 := by
  change (((Guarded.main (OrderedMemoryProvider.activeCircuit name spec provider binds canonical) inferInstance i).operations n).interactions.countP onByte) = _
  rw [Guarded.main_interactions,guarded]
  simp only [OrderedMemoryProvider.activeCircuit,OrderedMemoryProvider.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,List.countP_append,child,ordered name apart,add]

private theorem initial_width (s : MemorySnapshot) :
    (SnapshotMemoryEnsemble.ramView s : TransitionView (OrderedBoundary.channel (p := SP1Prime) SnapshotMemoryEnsemble.channelName)).component.rowOperations.interactions.countP onByte = 53 := by
  apply orderWidth _ (by decide) _ _ _ _ 48
  intro i n
  simp only [SnapshotRamProvider.circuit,SnapshotRamProvider.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    InitialMemoryRead.circuit,InitialMemoryRead.circuitNamed,List.countP_append,readWord _ _ (by decide : "sp1.native.initial_memory" ≠ "SP1Byte"),address]
  rfl

private theorem final_width : (original (.finalizer true) : Component F).rowOperations.interactions.countP onByte = 9 := by
  have ramChild (i : Var MemoryMsg F) (n : ℕ) : ((FinalRamProvider.circuit.main i).operations n).interactions.countP onByte = 4 := by
    simp only [FinalRamProvider.circuit,FinalRamProvider.main,FinalRamProvider.addressCircuit,circuit_norm,
      GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,List.countP_append,word,address]
    rfl
  have fin (i : Var (OrderedMemoryProvider.RowInput MemoryMsg) F) (n : ℕ) :
      ((OrderedFinalProvider.ramCircuit.main i).operations n).interactions.countP onByte = 9 :=
    orderWidth _ (by decide) _ _ _ _ 4 ramChild i n
  change ((((FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit).main
      (varFromOffset (OrderedMemoryProvider.RowInput MemoryMsg) 0)).operations (size (OrderedMemoryProvider.RowInput MemoryMsg))).interactions.countP onByte) = 9
  simp only [FinalMemoryReceipt.circuit,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,List.countP_append,fin]
  rfl

private theorem target_width (s : MemorySnapshot) : (MixedTargetMemory.checkComponent s true).rowOperations.interactions.countP onByte = 44 := by
  change (((Guarded.main (FinalRamCheck.activeCircuit s) (FinalRamCheck.guardSupported s) (varFromOffset FinalRamCheck.RowInput 0)).operations (size FinalRamCheck.RowInput)).interactions.countP onByte) = 44
  rw [Guarded.main_interactions,guarded]
  have changeWidth (i : Var FinalMemoryChange.Inputs F) (n : ℕ) :
      (((FinalMemoryChange.circuit true).main i).operations n).interactions.countP onByte = 0 :=
    none (FinalMemoryChange.circuit true).base (by rfl) i n
  simp only [FinalRamCheck.activeCircuit,FinalRamCheck.main,FinalRamValue.circuit,FinalRamValue.main,
    InitialMemoryRead.circuitNamed,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,List.countP_append,readWord _ _ (by decide : "sp1.native.target_memory" ≠ "SP1Byte"),
    Gadgets.Equality.main,List.countP_cons,changeWidth]
  rfl

/-- Actual Byte widths of the ordered RAM initializer, ordered RAM finalizer and target validator. -/
theorem ram_widths (image : ProgramImage) (initial final : ExecutionSnapshot) (finish : HostHintQueue.State F) :
    (SnapshotMemoryEnsemble.ramView initial.sail.memorySnapshot).component.channelWidth bus = 53 ∧
    (original (.finalizer true)).channelWidth bus = 9 ∧ (MixedTargetMemory.checkComponent final.sail.memorySnapshot true).channelWidth bus = 44 := by
  have init : (SnapshotMemoryEnsemble.ramView initial.sail.memorySnapshot).component ∈ (base image initial final finish).tables := by
    apply List.mem_of_mem_take (i := 6)
    rw [boundary_prefix]
    exact List.Mem.tail _ (List.Mem.head _)
  have fin := List.mem_of_getElem? (original_at image initial final finish (.finalizer true))
  have chk := List.mem_of_getElem? (WriteMixedFixedResources.registered_at image initial final finish (.check true))
  exact ⟨(named_width _ init).trans (initial_width _),(named_width _ fin).trans final_width,(named_width _ chk).trans (target_width _)⟩

open FormalModel.Shard WriteProbe.SparseBoundary

/-- Number of distinct RAM words in the generated boundary, including native read-only requests. -/
def ramCount (initial : ExecutionSnapshot) (stream : List MemoryHistoryAccess) (keys : List ℕ)
    (data : ProverData F) (hint : ProverHint F) : ℕ :=
  ((terminals initial.sail.memorySnapshot stream keys data hint).filter (fun r => r.ram == true)).length

private theorem slot_cost {image : ProgramImage} {initial final : ExecutionSnapshot} {finish : HostHintQueue.State F}
    (w : EnsembleWitness (base image initial final finish)) (i : Fin w.tables.length)
    (t : Table F) (registered : (base image initial final finish).tables[i.val]? = some t.component)
    (cells : (w.tables.map Table.table)[i.val]? = some t.table) {h k : ℕ}
    (height : t.length = h) (width : t.component.channelWidth bus = k) :
    w.tables[i.val].length * w.tables[i.val].component.channelWidth bus = h*k := by
  have comp := congrArg (fun cs : List (Component F) => cs[i.val]?) w.tables_map_component
  rw [List.getElem?_map,List.getElem?_eq_getElem i.isLt,Option.map_some] at cells comp
  rw [registered] at comp
  have rows := congrArg List.length (Option.some.inj cells)
  change w.tables[i.val].length = t.length at rows
  rw [rows,height,Option.some.inj comp,width]

variable {image : ProgramImage} {initial final : ExecutionSnapshot} {events : List ExecutionEvent}
    (run : ReleaseAdmissibleExecution (.native SP1Prime) SP1Prime image initial final events)
    {rows : List MixedCompiledRow}
    (routed : routeMixedRows? (policy SP1Prime image) image.program AccessFrontier.initial initial.realize events = some rows)
    (finish : HostHintQueue.State F) (data : ProverData F) (hint : ProverHint F) (header : SP1PublicIO F)
    (packets : List WriteObservations.Packet) (rest : WriteMixedControlTables.Remaining image initial final finish)

attribute [local irreducible] base WriteGeneratedByteClients.supervisor

/-- Three original generated RAM tables spend 106 Byte sites per padded distinct RAM word. -/
theorem supervisor_lower_bound :
    let w := WriteGeneratedByteClients.supervisor run routed finish data hint header packets rest
    let count := ramCount initial (MixedMemoryHistory.stream image initial events rows) (WriteBoundaryBuild.demandKeys events packets) data hint
    106 * WitnessGeneration.demandHeight count ≤ (w.interactionsWith bus).length := by
  intro w count
  let stream := MixedMemoryHistory.stream image initial events rows
  let keys := WriteBoundaryBuild.demandKeys events packets
  let canon := MixedMemoryHistory.canonical run.1 routed
  let ts := terminals initial.sail.memorySnapshot stream keys data hint
  let h := WitnessGeneration.demandHeight count
  let bound := terminal_count_fit true initial.sail.memorySnapshot stream keys canon data hint
  let incoming := initialTable initial.sail.memorySnapshot true ts data bound
  let outgoing := finalTable true ts data (terminals_fit true initial.sail.memorySnapshot stream keys canon data hint)
  let validator := WriteMixedFixedResources.table run routed data hint packets (.check true)
  have size : w.tables.length = 98 := w.same_length.symm.trans (base_length ..)
  let slot (n : Fin 98) : Fin w.tables.length := ⟨n.val,by rw [size]; exact n.isLt⟩
  let cost (i : Fin w.tables.length) := w.tables[i.val].length * w.tables[i.val].component.channelWidth bus
  obtain ⟨iw,fw,tw⟩ := ram_widths image initial final finish
  have first : (base image initial final finish).tables[1]? = some incoming.component := by
    rw [← List.getElem?_take_of_lt (by decide : 1 < 6),boundary_prefix]
    rfl
  have c₁ : cost (slot 1) = h * 53 :=
    slot_cost w (slot 1) incoming first (WriteGeneratedByteClients.rows_at_boundary run routed finish data hint header packets rest 1)
      (initialTable_length _ _ ts data _) iw
  have c₂ : cost (slot 4) = h * 9 :=
    slot_cost w (slot 4) outgoing (original_at image initial final finish (.finalizer true))
      (WriteGeneratedByteClients.rows_at_boundary run routed finish data hint header packets rest 4)
      (finalTable_length true ts data _) fw
  have c₃ : cost (slot 95) = h * 44 :=
    slot_cost w (slot 95) validator (WriteMixedFixedResources.registered_at image initial final finish (.check true))
      (by unfold w WriteGeneratedByteClients.supervisor; exact WriteMixedFixedResources.original_arrays run routed data hint packets header (WriteMixedControlTables.install run routed data rest) (.check true))
      (MixedTargetMemory.checkTable_length initial.sail.memorySnapshot final.sail.memorySnapshot true ts data bound) tw
  have unique : [slot 1,slot 4,slot 95].Nodup := by
    apply List.Nodup.of_map Fin.val
    change [1,4,95].Nodup
    decide
  have sum := w.selected_table_cost_le _ unique bus
  change cost (slot 1) + (cost (slot 4) + (cost (slot 95) + 0)) ≤ _ at sum
  rw [c₁,c₂,c₃,w.channelOccurrences_eq_length] at sum
  change 106 * h ≤ _
  omega

/-- Once the generated boundary has more than 2^24 RAM words, these three actual
tables alone exceed KoalaBear's Byte occurrence limit on every observer installation. -/
theorem assembled_overflow (suffix : List (Table F)) (registered : suffix.map Table.component = WriteObservationAssembly.tables initial final)
    (large : 2^24 < ramCount initial (MixedMemoryHistory.stream image initial events rows) (WriteBoundaryBuild.demandKeys events packets) data hint) :
    let w := WriteGeneratedByteClients.supervisor run routed finish data hint header packets rest
    SP1Prime ≤ ((WriteObservationAssembly.build w suffix registered).interactionsWith bus).length := by
  intro w
  let n := ramCount initial (MixedMemoryHistory.stream image initial events rows) (WriteBoundaryBuild.demandKeys events packets) data hint
  change 2^24 < n at large
  obtain ⟨e,height⟩ := WitnessGeneration.demandHeight_power (show n ≠ 0 by omega)
  have lt := large.trans_le (WitnessGeneration.demandHeight_bounds n).1
  rw [height,Nat.pow_lt_pow_iff_right (by decide)] at lt
  have lo : 2^25 ≤ 2^e := Nat.pow_le_pow_right (by decide) lt
  have spent := supervisor_lower_bound run routed finish data hint header packets rest
  change 106 * WitnessGeneration.demandHeight n ≤ (w.interactionsWith bus).length at spent
  rw [height] at spent
  rw [WriteObservationAssembly.build_ledger,installSources_ledger _ _ (fun e => (by decide : bus.name ≠ WriteProbe.readbackChannel.toRaw.name) (congrArg RawChannel.name e)),List.length_append]
  apply (show SP1Prime ≤ 106 * 2^25 by decide).trans
  omega

end SP1Clean.Export.WriteSparseByteCapacity
