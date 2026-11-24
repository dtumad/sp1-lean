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

private theorem ordered (name : String) (apart : name ≠ "SP1Byte") (i : Var OrderedBoundary.Inputs F) (n : ℕ) :
    (((OrderedBoundary.circuit name).main i).operations n).interactions.all allowed = true := by
  simp only [OrderedBoundary.circuit,OrderedBoundary.main,circuit_norm,
    FormalAssertion.toSubcircuit_interactions,List.all_append,word,cmp]
  simp [allowed,OrderedBoundary.channel,apart,circuit_norm]

private theorem orderedProvider {I : TypeMap} [ProvableType I] (name : String) (apart : name ≠ "SP1Byte")
    (spec : MemoryMsg F → Prop) (provider : GeneralFormalCircuit F I MemoryMsg) [Guarded.Supported provider]
    (binds : ∀ i o d, provider.Spec i o d → spec o) (canonical : ∀ r, spec r → MemoryBoundary.CanonicalSpec r)
    (child : ∀ i n, ((provider.main i).operations n).interactions.all allowed = true)
    (i : Var (OrderedMemoryProvider.RowInput I) F) (n : ℕ) :
    (((OrderedMemoryProvider.circuit name spec provider binds canonical).main i).operations n).interactions.all allowed = true := by
  change (((Guarded.main (OrderedMemoryProvider.activeCircuit name spec provider binds canonical) inferInstance i).operations n).interactions.all allowed) = true
  rw [Guarded.main_interactions,guard_all]
  simp only [OrderedMemoryProvider.activeCircuit,OrderedMemoryProvider.main,circuit_norm,
    GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,
    List.all_append,child,ordered name apart,add]

private theorem address (i : Var AddressOperation.Inputs F) (n : ℕ) :
    ((AddressOperation.circuit.main i).operations n).interactions.all allowed = true := by
  simp only [AddressOperation.circuit,AddressOperation.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,
    AddrAddOperation.circuit,AddrAddOperation.main,Gadgets.Equality.main]
  rfl

private theorem headReg (s : MemorySnapshot) : Checked (SnapshotMemoryEnsemble.registerView s).component := by
  apply orderedProvider _ (by decide)
  intro i n
  rfl

private theorem headRam (s : MemorySnapshot) : Checked (SnapshotMemoryEnsemble.ramView s).component := by
  apply orderedProvider _ (by decide)
  intro i n
  simp only [SnapshotRamProvider.circuit,SnapshotRamProvider.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
    InitialMemoryRead.circuit,InitialMemoryRead.circuitNamed,List.all_append,readWord,address]
  rfl

private theorem boundarySeal (name : String) (apart : name ≠ "SP1Byte") :
    Checked (OrderedMemoryEnsemble.terminalView name apart).component := by
  change (((OrderedBoundaryEnd.main name _ (varFromOffset OrderedBoundary.TerminalInputs 0)).operations (size OrderedBoundary.TerminalInputs)).interactions.all allowed) = true
  simp only [OrderedBoundaryEnd.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,ordered name apart]

private theorem finalizer (ram : Bool) : Checked (original (.finalizer ram)) := by
  have reg (i : Var MemoryMsg F) (n : ℕ) : ((FinalRegisterProvider.circuit.main i).operations n).interactions.all allowed = true :=
    other FinalRegisterProvider.circuit.base (by rfl) i n
  have ramChild (i : Var MemoryMsg F) (n : ℕ) : ((FinalRamProvider.circuit.main i).operations n).interactions.all allowed = true := by
    simp only [FinalRamProvider.circuit,FinalRamProvider.main,FinalRamProvider.addressCircuit,circuit_norm,
      GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,List.all_append,word,address]
    rfl
  have receipt (tag : Bool) (child : GeneralFormalCircuit F (OrderedMemoryProvider.RowInput MemoryMsg) MemoryMsg)
      (checked : ∀ i n, ((child.main i).operations n).interactions.all allowed = true)
      (i : Var (OrderedMemoryProvider.RowInput MemoryMsg) F) (n : ℕ) :
      ((((FinalMemoryReceipt.circuit tag child).main i).operations n).interactions.all allowed) = true := by
    simp only [FinalMemoryReceipt.circuit,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,List.all_append,checked]
    cases tag <;> rfl
  cases ram
  · apply receipt false OrderedFinalProvider.registerCircuit
    exact orderedProvider _ (by decide) _ _ _ _ reg
  · apply receipt true OrderedFinalProvider.ramCircuit
    exact orderedProvider _ (by decide) _ _ _ _ ramChild

private theorem hostWord (last : Bool) : Checked (original (.host (.word last))) := by
  have range (n : ℕ) (hn : 2^n < SP1Prime) (i : Var field F) (o : ℕ) :
      (((Gadgets.ToBits.rangeCheck n hn).main i).operations o).interactions.all allowed = true :=
    other (Gadgets.ToBits.rangeCheck n hn).base (by rfl) i o
  have access (i : Var Readers.MemoryAccess.Inputs F) (o : ℕ) :
      ((Readers.MemoryAccess.circuit.main i).operations o).interactions.all allowed = true := by
    simp only [Readers.MemoryAccess.circuit,Readers.MemoryAccess.main,circuit_norm,FormalAssertion.toSubcircuit_interactions,Gadgets.Equality.main]
    rfl
  have ram (i : Var HostRamAccessChip.Inputs F) (o : ℕ) :
      ((HostRamAccessChip.circuit.main i).operations o).interactions.all allowed = true := by
    simp only [HostRamAccessChip.circuit,HostRamAccessChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,
      FormalAssertion.toSubcircuit_interactions,List.all_append,word,address,range,access]
    rfl
  change (((Guarded.main (HintReadWordChip.activeCircuit last) (HintReadWordChip.guardSupported last)
      (varFromOffset HintReadWordChip.RowInput 0)).operations (size HintReadWordChip.RowInput)).interactions.all allowed) = true
  rw [Guarded.main_interactions,guard_all]
  simp only [HintReadWordChip.activeCircuit,HintReadWordChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,List.all_append,ram,step]
  rfl

private theorem ecall : Checked (original (.host .ecall)) := by
  change (((HostCallChip.main (varFromOffset SyscallInstrsChip.Inputs 0)).operations (size SyscallInstrsChip.Inputs)).interactions.all allowed) = true
  simp only [HostCallChip.main,CoreSyscallChip.circuit,CoreSyscallChip.main,SyscallCodeGuard.circuit,SyscallInstrsChip.circuit,
    SyscallInstrsChip.main,circuit_norm,GeneralFormalCircuit.toSubcircuit_interactions,FormalAssertion.toSubcircuit_interactions,
    Readers.CPUState.circuit,Readers.CPUState.main,Readers.RegisterAccessCols.circuit,Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,Readers.RegisterAccessTimestamp.main,IsZeroOperation.circuit,IsZeroOperation.main,
    U16toU8OperationSafe.circuit,U16toU8OperationSafe.main,Gadgets.Equality.main,
    SyscallInstrsChip.CommitArm.circuit,SyscallInstrsChip.CommitArm.main,SyscallInstrsChip.DispatchArm.circuit,
    SyscallInstrsChip.DispatchArm.main,SyscallInstrsChip.FieldBoundArm.circuit,SyscallInstrsChip.FieldBoundArm.main,
    SyscallInstrsChip.PcArm.circuit,SyscallInstrsChip.PcArm.main,SyscallInstrsChip.WriteArm.circuit,SyscallInstrsChip.WriteArm.main,
    U16CompareOperation.circuit,U16CompareOperation.main]
  rfl

/-- Every source of a WRITE predecessor, including both HINT_READ word families, only
pulls Byte lookups on its original circuit. -/
theorem source (id : Source) {a : AbstractInteraction F}
    (seen : a ∈ (original id).operations.interactionsWith byteChannel.toRaw) : a.direction = .pull := by
  cases id with
  | ordinary id => exact InstalledAssembly.ordinary_byte_direction id seen
  | refresh => exact directions (c := original .refresh) (by rfl) seen
  | host fam => cases fam with
    | ecall => exact directions ecall seen
    | word last => exact directions (hostWord last) seen
  | finalizer ram => exact directions (finalizer ram) seen

private theorem first_six (image : ProgramImage) (initial final : ExecutionSnapshot) (finish : HostHintQueue.State F)
    {c : Component F} (inside : c ∈ (WriteSourceRegistry.base image initial final finish).tables.take 6) : Checked c := by
  rw [WriteSourceRegistry.boundary_prefix] at inside
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl | rfl | rfl | rfl
  · exact headReg _
  · exact headRam _
  · exact boundarySeal _ (by decide)
  · exact finalizer false
  · exact finalizer true
  · exact boundarySeal _ (by decide)

attribute [local irreducible] WriteSourceRegistry.base in
/-- At every physical original index outside the 23-provider window, all registered Byte
interactions are pulls. The window follows from the registry's actual residual positions. -/
theorem client (image : ProgramImage) (initial final : ExecutionSnapshot) (finish : HostHintQueue.State F)
    {c : Component F} {k : ℕ} (located : (WriteSourceRegistry.base image initial final finish).tables[k]? = some c)
    (outside : k < 32 ∨ 55 ≤ k) {a : AbstractInteraction F} (seen : a ∈ c.operations.interactionsWith byteChannel.toRaw) :
    a.direction = .pull := by
  by_cases first : k < 6
  · apply directions _ seen
    apply first_six image initial final finish
    apply List.mem_of_getElem? (i := k)
    rwa [List.getElem?_take_of_lt first]
  cases src : WriteSourceRegistry.sourceAt k with
  | some id =>
    have same := WriteSourceRegistry.original_at image initial final finish id
    rw [WriteSourceRegistry.position_of_sourceAt src,located] at same
    exact source id (Option.some.inj same ▸ seen)
  | none =>
    cases h : WriteMixedHostTables.indexAt k with
    | some id =>
      have same := WriteMixedHostTables.registered_at image initial final finish id
      rw [WriteMixedHostTables.position_of_indexAt h,located] at same
      exact host id (Option.some.inj same ▸ seen)
    | none =>
      cases f : WriteMixedFixedResources.indexAt k with
      | some id =>
        have pos : WriteMixedFixedResources.position id = k := eq_of_beq (List.find?_some (p := fun id => WriteMixedFixedResources.position id == k) f)
        have same := WriteMixedFixedResources.registered_at image initial final finish id
        rw [pos,located] at same
        exact fixed image initial final id (Option.some.inj same ▸ seen)
      | none =>
        cases ctrl : WriteMixedControlTables.indexAt k with
        | some id =>
          have pos : WriteMixedControlTables.position id = k := eq_of_beq (List.find?_some (p := fun id => WriteMixedControlTables.position id == k) ctrl)
          have same := WriteMixedControlTables.registered_at image initial final finish id
          rw [pos,located] at same
          exact control id (Option.some.inj same ▸ seen)
        | none =>
          have size := (List.getElem?_eq_some_iff.mp located).1
          have inRange : k ∈ (List.range' 6 (((WriteSourceRegistry.base image initial final finish).tables).drop 6).length).filter
              (fun j => (WriteSourceRegistry.sourceAt j).isNone && (WriteMixedHostTables.indexAt j).isNone &&
                (WriteMixedFixedResources.indexAt j).isNone && (WriteMixedControlTables.indexAt j).isNone) := by
            apply List.mem_filter.mpr
            refine ⟨List.mem_range'_1.mpr ?_,by simp [src,h,f,ctrl]⟩
            rw [List.length_drop]
            omega
          rw [WriteMixedControlTables.remaining_positions,List.mem_range'_1] at inRange
          omega

end SP1Clean.Export.WriteOriginalByteDirections
