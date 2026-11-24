import SP1Clean.Export.WriteByteLedger

/-! # Byte lookup directions of the original supervisor clients -/

namespace SP1Clean.Export.WriteOriginalByteDirections
open Circuit Air.Flat Semantics Soundness Machine TraceGen Channels WriteProbe.AccessInventory
private abbrev F := ZMod SP1Prime
private def allowed (a : AbstractInteraction F) : Bool := a.direction == .pull || a.channel.name != "SP1Byte"
private abbrev Checked (c : Component F) := c.rowOperations.interactions.all allowed = true

private theorem other {I O : TypeMap} [ProvableType I] [ProvableType O] (c : FormalCircuitBase F I O)
    (absent : c.channels.all (fun ch => ch.name != "SP1Byte") = true) (i : Var I F) (n : ℕ) :
    ((c.main i).operations n).interactions.all allowed = true := by
  apply List.all_eq_true.mpr
  intro a inside
  have declared := c.channels_subset i n (List.mem_map_of_mem (f := AbstractInteraction.channel) inside)
  simp only [allowed,List.all_eq_true.mp absent a.channel declared,Bool.or_true]

private theorem guard_all (e : Expression F) (xs : List (AbstractInteraction F)) :
    (xs.map (AbstractInteraction.guard e)).all allowed = xs.all allowed := by rw [List.all_map]; rfl

private theorem directions {c : Component F} (checked : Checked c) {i : AbstractInteraction F}
    (inside : i ∈ c.operations.interactionsWith byteChannel.toRaw) : i.direction = .pull := by
  have same := Operations.channel_eq_of_mem_interactionsWith inside
  have mem := List.mem_of_mem_filter inside
  rw [Component.interactions_eq] at mem
  have ok := List.all_eq_true.mp checked i mem
  simpa only [allowed,same,Channel.toRaw_name,byteChannel,bne_self_eq_false,Bool.or_false,beq_iff_eq] using ok

private theorem narrow {c : Component F} (absent : c.circuit.channels.all (fun ch => ch.name != "SP1Byte") = true) :
    Checked c := other c.circuit.base absent _ _

private theorem clock (i : Var ClockOrder.Inputs F) (n : ℕ) :
    (((ClockOrder.circuit (p := SP1Prime)).main i).operations n).interactions.all allowed = true :=
  other ClockOrder.circuit.base (by rfl) i n

private theorem word (i : Var Word F) (n : ℕ) :
    (((WordRangeCheck.circuit (p := SP1Prime)).main i).operations n).interactions.all allowed = true :=
  other WordRangeCheck.circuit.base (by rfl) i n

private theorem cmp (i : Var LtOperationUnsigned.Inputs F) (n : ℕ) :
    ((LtOperationUnsigned.circuit.main i).operations n).interactions.all allowed = true := by
  simp only [LtOperationUnsigned.circuit,LtOperationUnsigned.main,U16CompareOperation.circuit,U16CompareOperation.main,
    circuit_norm,FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.main]
  rfl

private theorem u16 (i : Var U16toU8OperationSafe.Inputs F) (n : ℕ) :
    ((U16toU8OperationSafe.circuit.main i).operations n).interactions.all allowed = true := by
  simp only [U16toU8OperationSafe.circuit,U16toU8OperationSafe.main,circuit_norm]
  rfl

private theorem bound (b : ℕ) (fit : b < 2^64) (i : Var BoundedWord.Inputs F) (n : ℕ) :
    (((BoundedWord.circuit b fit).main i).operations n).interactions.all allowed = true := by
  simp only [BoundedWord.circuit,BoundedWord.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,List.all_append,cmp,word]

private theorem bank (deferred : Bool) (slot : Fin 8) : Checked (WriteMixedHostTables.component (.bank deferred (some slot))) := by
  change (((Guarded.main (HostCommitChip.activeCircuit deferred slot) inferInstance (varFromOffset HostCommitChip.RowInput 0)).operations (size HostCommitChip.RowInput)).interactions.all allowed) = true
  rw [Guarded.main_interactions,guard_all]
  cases deferred <;>
    simp only [HostCommitChip.activeCircuit,HostCommitChip.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
      GeneralFormalCircuit.toSubcircuit_interactions,List.all_append,Gadgets.Equality.main,clock,bound,u16]
  all_goals rfl

private theorem bank_end (d : Bool) : Checked (WriteMixedHostTables.component (.bank d none)) := by
  apply other (HostCommitBoundary.terminal d).base
  cases d <;> rfl

private theorem add (i : Var AddOperation.Inputs F) (n : ℕ) :
    ((AddOperation.circuit.main i).operations n).interactions.all allowed = true := by
  simp only [AddOperation.circuit,AddOperation.main,circuit_norm]
  rfl

private theorem observation (i : Fin 4) : Checked (WriteMixedHostTables.component (.observation i)) := by
  fin_cases i
  · change (((Guarded.main SP1Clean.OrdinaryObservation.circuit inferInstance (varFromOffset SP1Clean.OrdinaryObservation.RowInput 0)).operations (size SP1Clean.OrdinaryObservation.RowInput)).interactions.all allowed) = true
    rw [Guarded.main_interactions,guard_all]
    simp only [SP1Clean.OrdinaryObservation.circuit,SP1Clean.OrdinaryObservation.main,circuit_norm,
      GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,List.all_append,clock,word,add]
    rfl
  all_goals apply other _ (by rfl)

private theorem lookupWord (m : ByteMemory) (k : String) (i : Var Word F) (n : ℕ) :
    ((InitialMemoryLookup.main m (2^48) i k).operations n).interactions.all allowed = true := by
  simp only [InitialMemoryLookup.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    List.all_append,word,cmp,List.all_cons]
  rfl

private theorem readWord (m : ByteMemory) (k : String) (i : Var Word F) (n : ℕ) :
    ((InitialMemoryRead.main m i k).operations n).interactions.all allowed = true := by
  simp only [InitialMemoryRead.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions,InitialMemoryLookup.circuitNamed,
    List.all_append,lookupWord,List.all_flatten]
  apply List.all_eq_true.mpr
  intro ys inside
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp inside
  simp only [List.all_append,add,lookupWord,Bool.and_self]

private theorem targetRAM (s : MemorySnapshot) : Checked (MixedTargetMemory.checkComponent s true) := by
  change (((Guarded.main (FinalRamCheck.activeCircuit s) (FinalRamCheck.guardSupported s) (varFromOffset FinalRamCheck.RowInput 0)).operations (size FinalRamCheck.RowInput)).interactions.all allowed) = true
  rw [Guarded.main_interactions,guard_all]
  have changeAllowed (i : Var FinalMemoryChange.Inputs F) (n : ℕ) :
      (((FinalMemoryChange.circuit true).main i).operations n).interactions.all allowed = true :=
    other (FinalMemoryChange.circuit true).base (by rfl) i n
  simp only [FinalRamCheck.activeCircuit,FinalRamCheck.main,FinalRamValue.circuit,FinalRamValue.main,
    InitialMemoryRead.circuitNamed,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,List.all_append,readWord,Gadgets.Equality.main,List.all_cons,changeAllowed]
  rfl

/-- ROM, source/target Memory, both permission tables, target checks, and the two fixed
hint inventories contribute only physical reads on Byte. -/
theorem fixed (image : ProgramImage) (source target : ExecutionSnapshot) (id : WriteMixedFixedResources.Index)
    {a : AbstractInteraction F} (seen : a ∈ (WriteMixedFixedResources.component image source target id).operations.interactionsWith byteChannel.toRaw) : a.direction = .pull := by
  apply directions _ seen
  rcases id with _ | (_|_) | (_|_) | (_|_) | (_|_) | (_|_)
  · apply narrow
    change ((FixedProgramProvider.Preprocessed.circuit (p := SP1Prime) image).channels.all _) = true
    rw [FixedProgramProvider.Preprocessed.circuit_channels]
    rfl
  · apply narrow
    change ((source.sail.memorySnapshot.registerTable (p := SP1Prime)).provider.channels.all _) = true
    simp only [GeneralFormalCircuit.channels,StaticTable.provider,circuit_norm,MemorySnapshot.registerTable,StaticTable.channel,StaticTable.ofRows]
    rfl
  · apply narrow; rfl
  · apply narrow
    change (((WritePermissionProvider.circuit (p := SP1Prime) image).channels).all _) = true
    simp only [GeneralFormalCircuit.channels,WritePermissionProvider.circuit,Guarded.circuit_channelsWithGuarantees,
      Guarded.circuit_channelsWithRequirements,WritePermissionProvider.activeCircuit,circuit_norm,
      StaticTable.channel,ProgramImage.writePermissionTable,StaticTable.ofRows]
    rfl
  · apply narrow
    change (image.writePermissionTable (p := SP1Prime)).provider.channels.all _ = true
    simp only [GeneralFormalCircuit.channels,StaticTable.provider,circuit_norm,ProgramImage.writePermissionTable,StaticTable.channel,StaticTable.ofRows]
    rfl
  · apply narrow; rfl
  · apply narrow; rfl
  · apply narrow; rfl
  · exact targetRAM _
  · apply narrow; rfl
  · apply narrow; rfl

private theorem addrAdd (i : Var AddrAddOperation.Inputs F) (n : ℕ) :
    ((AddrAddOperation.circuit.main i).operations n).interactions.all allowed = true := by
  simp only [AddrAddOperation.circuit,AddrAddOperation.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.main]
  rfl

private theorem step (last : Bool) (i : Var HintReadStep.Inputs F) (n : ℕ) :
    (((HintReadStep.circuit last).main i).operations n).interactions.all allowed = true := by
  simp only [HintReadStep.circuit,HintReadStep.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    List.all_append,word,addrAdd,List.all_cons]
  rfl

private theorem span (i : Var HintReadSpan.Inputs F) (n : ℕ) :
    ((HintReadSpan.circuit.main i).operations n).interactions.all allowed = true := by
  have div (i : Var AddressDiv8.Inputs F) (n : ℕ) :
      ((AddressDiv8.circuit.main i).operations n).interactions.all allowed = true := other AddressDiv8.circuit.base (by rfl) i n
  have ord (i : Var AddressOrder.Inputs F) (n : ℕ) :
      ((AddressOrder.circuit.main i).operations n).interactions.all allowed = true := other AddressOrder.circuit.base (by rfl) i n
  simp only [HintReadSpan.circuit,HintReadSpan.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,List.all_append,div,ord,addrAdd]

private theorem readHint : Checked (WriteMixedControlTables.component .hintRead) := by
  change (((Guarded.main HostHintReadChip.circuit inferInstance (varFromOffset HostHintReadChip.RowInput 0)).operations (size HostHintReadChip.RowInput)).interactions.all allowed) = true
  rw [Guarded.main_interactions,guard_all]
  simp only [HostHintReadChip.circuit,HostHintReadChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,List.all_append,Gadgets.Equality.main,clock,span,step]
  rfl

private theorem padding : Checked (WriteMixedControlTables.component .haltPadding) := by
  change (((HaltPaddingChip.main (varFromOffset HaltChip.Inputs 0)).operations (size HaltChip.Inputs)).interactions.all allowed) = true
  simp only [HaltPaddingChip.main,HaltChip.circuit,HaltChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    FormalAssertion.toSubcircuit_interactions,Readers.RegisterAccessCols.circuit,Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,Readers.RegisterAccessTimestamp.main,Readers.CPUState.circuit,Readers.CPUState.main]
  rfl

private theorem hostHalt : Checked (WriteMixedControlTables.component .halt) := by
  change (((HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0)).operations (size HostHaltChip.Inputs)).interactions.all allowed) = true
  simp only [HostHaltChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,List.all_append,Gadgets.Equality.main,bound]
  rfl

/-- Clock normalization, checkpoint padding and all five host control receiver forms only pull Byte. -/
theorem control (id : WriteMixedControlTables.Index) {a : AbstractInteraction F}
    (seen : a ∈ (WriteMixedControlTables.component id).operations.interactionsWith byteChannel.toRaw) : a.direction = .pull := by
  apply directions _ seen
  rcases id with _ | _ | _ | _ | _ | (_|_)
  · change (((StateBumpChip.main (varFromOffset StateBumpChip.Inputs 0)).operations (size StateBumpChip.Inputs)).interactions.all allowed) = true
    simp only [StateBumpChip.main,circuit_norm]
    rfl
  · exact padding
  · exact hostHalt
  · apply narrow; rfl
  · exact readHint
  · apply narrow; rfl
  · apply narrow; rfl

/-- Both commitment banks and all four ordinary observation components are genuine Byte readers. -/
theorem host (id : WriteMixedHostTables.Index) {a : AbstractInteraction F}
    (seen : a ∈ (WriteMixedHostTables.component id).operations.interactionsWith byteChannel.toRaw) : a.direction = .pull := by
  apply directions _ seen
  rcases id with ⟨d, _ | s⟩ | i
  · exact bank_end d
  · exact bank d s
  · exact observation i

end SP1Clean.Export.WriteOriginalByteDirections
