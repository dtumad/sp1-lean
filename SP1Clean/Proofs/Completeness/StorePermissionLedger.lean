import SP1Clean.Proofs.Completeness.StorePermissionRows

/-! # Signed byte requests of generated ordinary instruction buckets

The four store layouts recover the original address gadget at the actual compiled operands.
Every active physical occurrence is a unit pull for a byte of the naturally aligned write.
-/

namespace SP1Clean.TraceGen.StorePermissionRows

open Circuit Air.Flat Semantics Soundness Trace WritePermissionProvider

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

/-- Canonical byte-permission pulls for the actual routed event. -/
def requests (r : RoutedEvent) : List (Interaction F) :=
  (r.storeBytes.map (Address.ofNat (p := SP1Prime))).map channel.pulledValue

private theorem stored_address {input : AddressOperation.Inputs F} {cols : Circuits.Types.AddressOperation F}
    (e : MemoryEvent) (fits : e.addr < 2 ^ 48) (spec : AddressOperation.Spec input cols)
    (base : input.b = wordOfNat e.b) (imm : input.cc = wordOfNat e.imm) :
    cols.addr_operation.value = Address.ofNat e.addr := by
  obtain ⟨low,mid,high⟩ := AddressOperation.limbBounds_of_spec spec
  have bounds : Address.Bounded cols.addr_operation.value := by
    intro i
    fin_cases i <;> assumption
  have addr := spec.1
  rw [base,imm,wordOfNat_toNat,wordOfNat_toNat] at addr
  have packed : Address.toNat cols.addr_operation.value = e.addr := by
    unfold Address.toNat MemoryEvent.addr at *
    omega
  exact (Address.ofNat_toNat bounds).symm.trans (congrArg Address.ofNat packed)

private theorem range_values (address width : ℕ) {fields : fields 3 F} (packed : fields = Address.ofNat address)
    (within : ∀ i < width, address % 2 ^ 16 + i < 2 ^ 16) :
    List.ofFn (fun i : Fin width => channel.pulledIfValue 1 (Address.offset fields (i.val : F))) =
      ((List.range' address width).map (Address.ofNat (p := SP1Prime))).map channel.pulledValue := by
  subst fields
  apply List.ext_getElem
  · simp
  intro i lhs _
  have inside : i < width := by simpa using lhs
  simp only [List.getElem_ofFn,List.getElem_map,List.getElem_range',Nat.one_mul]
  exact congrArg channel.pulledValue (Address.offset_ofNat _ _ (within i inside))

private theorem active_values (id : InstructionChipId) (e : id.Event) (valid : id.Valid e)
    (cols : (supportedChipFor id).kind.Cols F) (data : ProverData F)
    (spec : ∀ ram, RoutedEvent.memoryEvent? ⟨id,e⟩ = some ram →
      (installed id).circuit.Spec (InstalledInstructionTables.activeInput id e) cols data) :
    values ((supportedChipFor id).kind.view (InstalledInstructionTables.activeInput id e) cols) = requests ⟨id,e⟩ := by
  cases id <;> try rfl
  case jal | jalr | uType =>
    exact no_write_values _ (CommitEffect.destination_memWrite _)
  case storeByte =>
    have original : StoreByteChip.Spec e.toStoreByteInputs cols data := spec e rfl
    apply range_values e.addr 1 (stored_address e valid.addr_lt (original.1.2.2.2 rfl) rfl rfl)
    intro i inside
    omega
  case storeHalf =>
    have original : StoreHalfChip.Spec e.toStoreHalfInputs cols data := spec e rfl
    apply range_values e.addr 2 (stored_address e valid.1.addr_lt (original.1.2.2.2 rfl) rfl rfl)
    intro i inside
    have align : e.addr % 2 = 0 := valid.2
    omega
  case storeWord =>
    have original : StoreWordChip.Spec e.toStoreWordInputs cols data := spec e rfl
    apply range_values e.addr 4 (stored_address e valid.1.addr_lt (original.1.2.2.2 rfl) rfl rfl)
    intro i inside
    have align : e.addr % 4 = 0 := valid.2
    omega
  case storeDouble =>
    have original : StoreDoubleChip.Spec e.toStoreDoubleInputs cols data := spec e rfl
    apply range_values e.addr 8 (stored_address e valid.1.addr_lt (original.1.2.2.2 rfl) rfl rfl)
    intro i inside
    have align : e.addr % 8 = 0 := valid.2
    omega

private theorem built_active (id : InstructionChipId) (e : id.Event) (valid : id.Valid e)
    (data evaluation : ProverData F) (hint : ProverHint F) :
    let input := InstalledInstructionTables.activeInput id e
    let env := Environment.fromArray ((installed id).buildRow input data hint) evaluation
    (installed id).operations.interactionValuesWith channel.toRaw env = requests ⟨id,e⟩ := by
  intro input env
  rw [emitted]
  change values ((supportedChipFor id).kind.view ((installed id).rowInput env) ((supportedChipFor id).table.rowOutput env)) = _
  rw [(installed id).rowInput_buildRow input data evaluation hint]
  exact active_values id e valid _ data (fun _ h => InstalledInstructionTables.active_memory_spec id e valid h data evaluation hint)

private theorem inactive_values (row : RowView F) (off : row.is_real = 0) (msg : Array F) :
    balanceOf (values row) msg = 0 := by
  cases h : row.commit.memWrite with
  | none => rw [no_write_values row h]; rfl
  | some w =>
    let addrs := List.ofFn (fun i : Fin w.width => Address.offset w.addr (i.val : F))
    have pulls : values row = addrs.map (channel.pulledIfValue 0) := by
      simp only [values,h,Option.toList_some,List.flatMap_singleton,off,addrs,List.map_ofFn,Function.comp_def]
    rw [pulls]
    induction addrs with
    | nil => rfl
    | cons a rest ih =>
      rw [List.map_cons,balanceOf_cons,ih,add_zero]
      simp [Channel.pulledIfValue,Interaction.signedMult]

/-- Signed physical ledger of one installed instruction bucket, with every actual padding row
retained and all addresses recovered from the original generated output columns. -/
theorem table_sum (id : InstructionChipId) (events : List id.Event)
    (valid : ∀ e ∈ events, id.Valid e) (data : ProverData F) (hint : ProverHint F) (fit) (msg : Array F) :
    balanceOf ((InstalledInstructionTables.table id events data hint fit).interactionsWith channel.toRaw) msg =
      balanceOf (events.flatMap (fun e => requests ⟨id,e⟩)) msg := by
  let c := installed id
  let d := c.inputData (InstalledInstructionTables.inputs id events) data
  let pulls (input : c.Input F) := c.operations.interactionValuesWith channel.toRaw
    (Environment.fromArray (c.buildRow input d hint) d)
  let pad := InstalledInstructionTables.paddingInput id
  have zero : balanceOf (pulls pad) msg = 0 := by
    change balanceOf ((installed id).operations.interactionValuesWith channel.toRaw _) msg = 0
    rw [emitted]
    exact inactive_values _ (InstalledInstructionTables.padding_inactive id d d hint) msg
  have padding (n : ℕ) : balanceOf ((List.replicate n pad).flatMap pulls) msg = 0 := by
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ,List.flatMap_cons,balanceOf_append,zero,ih,add_zero]
  rw [InstalledInstructionTables.table,Table.build_interactions]
  change balanceOf ((InstalledInstructionTables.inputs id events).flatMap pulls) msg = _
  rw [InstalledInstructionTables.inputs,List.flatMap_append,balanceOf_append,padding,add_zero,List.flatMap_map]
  exact congrArg (fun xs => balanceOf xs msg) (List.flatMap_congr (fun e he => built_active id e (valid e he) d d hint))

end SP1Clean.TraceGen.StorePermissionRows
