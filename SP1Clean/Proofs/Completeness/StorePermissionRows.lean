import SP1Clean.Proofs.Completeness.MemoryInstructionRows
import SP1Clean.Proofs.Completeness.InstructionEvent
import SP1Clean.Proofs.Completeness.PermissionTables
import SP1Clean.Soundness.ProtectedStorePermissions
import SP1Clean.Soundness.StoreWritePolicy

/-! # Byte permissions emitted by the four installed ordinary STORE tables

The protected table uses the real output of the original address gadget. Its three canonical
limbs select the effective Sail address and each byte of the store's actual width.
-/

namespace SP1Clean.TraceGen.StorePermissionRows

open Circuit Air.Flat Soundness Trace Semantics WritePermissionProvider

private abbrev F := ZMod SP1Prime
private abbrev installed := ProtectedOrdinaryReceipt.component (p := SP1Prime)

/-- Canonical input layout for the dependent registry. -/
local instance permissionRowInput (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Inputs :=
  (supportedChipFor (p := SP1Prime) id).kind.provableInputs

/-- Canonical output layout for the dependent registry. -/
local instance permissionRowOutput (id : InstructionChipId) : ProvableType (supportedChipFor (p := SP1Prime) id).kind.Cols :=
  (supportedChipFor (p := SP1Prime) id).kind.provableCols

/-- Every requested byte of this committed store. -/
def values (row : RowView F) : List (Interaction F) :=
  row.commit.memWrite.toList.flatMap fun w => List.ofFn (fun i : Fin w.width =>
    channel.pulledIfValue row.is_real (Address.offset w.addr (i.val : F)))

private theorem eval_offsets (env : Environment F) (gate : Expression F) (address : Var (fields 3) F) (n : ℕ) :
    (List.ofFn (fun i : Fin n => (channel.pulledIf gate (Address.offset address (.const (i.val : F)))).toRaw)).map (fun a => a.eval env) =
      List.ofFn (fun i : Fin n => channel.pulledIfValue (eval env gate) (Address.offset (eval env address) (i.val : F))) := by
  simp only [List.map_ofFn,Function.comp_def,Channel.eval_pulledIf]
  apply congrArg List.ofFn
  funext i
  have offset : eval env (Address.offset address (.const (i.val : F))) = Address.offset (eval env address) (i.val : F) := by
    simp only [Address.offset, circuit_norm]
  rw [offset]

private def view (id : InstructionChipId) (env : Environment F) : RowView F :=
  let c := (supportedChipFor id).table
  (supportedChipFor id).kind.view (c.rowInput env) (c.rowOutput env)

private theorem other_channel : (channel (p := SP1Prime)).toRaw ≠ InstructionReceipt.channel.toRaw := by
  intro same
  exact (by decide : "SP1WritePermission" ≠ "SP1OrdinaryStateReceipt") (congrArg RawChannel.name same)

private theorem byte_emitted (env : Environment F) :
    (installed .storeByte).operations.interactionValuesWith channel.toRaw env = values (view .storeByte env) := by
  rw [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions _ _ other_channel, Component.interactionsWith_eq]
  change (((ProtectedStore.byte.main (varFromOffset StoreByteChip.Inputs 0)).operations (size StoreByteChip.Inputs)).interactionsWith channel.toRaw).map _ = _
  rw [WritePermission.byte_emission]
  simp only [List.map_singleton,Channel.eval_pulledIf]
  let input := varFromOffset (F := F) StoreByteChip.Inputs 0
  let cols := (StoreByteChip.circuit input).output (size StoreByteChip.Inputs)
  have real : eval env input.is_real = (eval env input).is_real := by
    rw [StoreByteChip.eval_inputs]
  have addr : eval env cols.address_operation.addr_operation.value = (eval env cols).address_operation.addr_operation.value := by
    provable_struct_simp
  change [channel.pulledIfValue (eval env input.is_real) (eval env cols.address_operation.addr_operation.value)] = _
  rw [real,addr]
  change _ = List.ofFn (fun i : Fin 1 => channel.pulledIfValue ((installed .storeByte).rowInput env).is_real
    (Address.offset ((installed .storeByte).rowOutput env).address_operation.addr_operation.value (i.val : F)))
  simp only [List.ofFn_succ,List.ofFn_zero,Fin.val_zero,Nat.cast_zero,Address.offset_zero]
  rw [show eval env input = (installed .storeByte).rowInput env from eval_varFromOffset_valueFromOffset _ 0 env]
  rfl


private theorem half_emitted (env : Environment F) :
    (installed .storeHalf).operations.interactionValuesWith channel.toRaw env = values (view .storeHalf env) := by
  rw [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions _ _ other_channel, Component.interactionsWith_eq]
  change (((ProtectedStore.half.main (varFromOffset StoreHalfChip.Inputs 0)).operations (size StoreHalfChip.Inputs)).interactionsWith channel.toRaw).map _ = _
  rw [WritePermission.half_emission,eval_offsets]
  let input := varFromOffset (F := F) StoreHalfChip.Inputs 0
  let cols := (StoreHalfChip.circuit input).output (size StoreHalfChip.Inputs)
  have gate : eval env input.is_real = (eval env input).is_real := by rw [StoreHalfChip.eval_inputs]
  have addr : eval env cols.address_operation.addr_operation.value = (eval env cols).address_operation.addr_operation.value := by
    provable_struct_simp
  change List.ofFn (fun i : Fin 2 => channel.pulledIfValue (eval env input.is_real)
    (Address.offset (eval env cols.address_operation.addr_operation.value) (i.val : F))) = _
  rw [gate,addr,show eval env input = (installed .storeHalf).rowInput env from eval_varFromOffset_valueFromOffset _ 0 env]
  rfl


private theorem word_emitted (env : Environment F) :
    (installed .storeWord).operations.interactionValuesWith channel.toRaw env = values (view .storeWord env) := by
  rw [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions _ _ other_channel, Component.interactionsWith_eq]
  change (((ProtectedStore.word.main (varFromOffset StoreWordChip.Inputs 0)).operations (size StoreWordChip.Inputs)).interactionsWith channel.toRaw).map _ = _
  rw [WritePermission.word_emission,eval_offsets]
  let input := varFromOffset (F := F) StoreWordChip.Inputs 0
  let cols := (StoreWordChip.circuit input).output (size StoreWordChip.Inputs)
  have gate : eval env input.is_real = (eval env input).is_real := by rw [StoreWordChip.eval_inputs]
  have addr : eval env cols.address_operation.addr_operation.value = (eval env cols).address_operation.addr_operation.value := by
    provable_struct_simp
  change List.ofFn (fun i : Fin 4 => channel.pulledIfValue (eval env input.is_real)
    (Address.offset (eval env cols.address_operation.addr_operation.value) (i.val : F))) = _
  rw [gate,addr,show eval env input = (installed .storeWord).rowInput env from eval_varFromOffset_valueFromOffset _ 0 env]
  rfl


private theorem double_emitted (env : Environment F) :
    (installed .storeDouble).operations.interactionValuesWith channel.toRaw env = values (view .storeDouble env) := by
  rw [Operations.interactionValuesWith, ProtectedOrdinaryReceipt.interactions _ _ other_channel, Component.interactionsWith_eq]
  change (((ProtectedStore.double.main (varFromOffset StoreDoubleChip.Inputs 0)).operations (size StoreDoubleChip.Inputs)).interactionsWith channel.toRaw).map _ = _
  rw [WritePermission.double_emission,eval_offsets]
  let input := varFromOffset (F := F) StoreDoubleChip.Inputs 0
  let cols := (StoreDoubleChip.circuit input).output (size StoreDoubleChip.Inputs)
  have gate : eval env input.is_real = (eval env input).is_real := by rw [StoreDoubleChip.eval_inputs]
  have addr : eval env cols.address_operation.addr_operation.value = (eval env cols).address_operation.addr_operation.value := by
    provable_struct_simp
  change List.ofFn (fun i : Fin 8 => channel.pulledIfValue (eval env input.is_real)
    (Address.offset (eval env cols.address_operation.addr_operation.value) (i.val : F))) = _
  rw [gate,addr,show eval env input = (installed .storeDouble).rowInput env from eval_varFromOffset_valueFromOffset _ 0 env]
  rfl

/-- A decoded row that never writes RAM emits no byte requests. -/
theorem no_write_values (row : RowView F) (empty : row.commit.memWrite = none) : values row = [] := by
  simp [values,empty]

private theorem original_silent (id : InstructionChipId) :
    channel.toRaw ∉ (supportedChipFor (p := SP1Prime) id).circuit.channels := by
  have member : (supportedChipFor (p := SP1Prime) id).table ∈ sp1Tables :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨id,InstructionChipId.mem_all id,rfl⟩,rfl⟩
  intro used
  have listed := sp1Tables_channels_subset _ member used
  simp only [sp1CoreChannels_eq,List.mem_cons,List.not_mem_nil,or_false] at listed
  rcases listed with h | h | h | h | h <;>
    exact Bool.noConfusion (congrArg (fun ch => ch.name == "SP1WritePermission") h)

private theorem unchanged (id : InstructionChipId) (env : Environment F)
    (same : ProtectedOrdinaryReceipt.provider (p := SP1Prime) id = (supportedChipFor id).circuit)
    (empty : values (view id env) = []) :
    (installed id).operations.interactionValuesWith channel.toRaw env = values (view id env) := by
  rw [Operations.interactionValuesWith,ProtectedOrdinaryReceipt.interactions _ _ other_channel,
    Component.interactionsWith_eq,same,empty]
  change (((supportedChipFor id).circuit.main (varFromOffset _ 0)).operations (size (supportedChipFor id).kind.Inputs) |>.interactionsWith channel.toRaw).map _ = []
  rw [InteractionRecovery.interactionsWith_main_eq_nil (supportedChipFor id).circuit.base _ _ _ (original_silent id)]
  rfl

/-- The complete physical permission ledger of any original instruction row, including inactive
STORE occurrences and all 21 silent instruction families. -/
theorem emitted (id : InstructionChipId) (env : Environment F) :
    (installed id).operations.interactionValuesWith channel.toRaw env =
      values ((supportedChipFor id).kind.view ((supportedChipFor id).table.rowInput env) ((supportedChipFor id).table.rowOutput env)) := by
  cases id
  case storeByte => exact byte_emitted env
  case storeHalf => exact half_emitted env
  case storeWord => exact word_emitted env
  case storeDouble => exact double_emitted env
  case jal | jalr | uType =>
    apply unchanged _ env rfl
    exact no_write_values _ (CommitEffect.destination_memWrite _)
  all_goals exact unchanged _ env rfl rfl

end SP1Clean.TraceGen.StorePermissionRows
