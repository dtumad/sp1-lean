import SP1Clean.Soundness.ProtectedLocalCorePermissions
import SP1Clean.Soundness.RomWriteProtection

/-! # Actual store footprints are permitted by the local AIR

The permission pulls and semantic write view use the same original chip output. Evaluating the
symbolic byte offsets therefore authenticates every byte in `MemWrite.covers`, including partial
writes beside ROM. These physical-row lemmas supply `RowWritePermitted` without a semantic
permission hypothesis or any assumption about unrelated Sail steps.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
private theorem eval_offset (env : Environment (ZMod p)) (address : Var (fields 3) (ZMod p))
    (index : ZMod p) :
    eval env (Address.offset address (.const index)) = Address.offset (eval env address) index := by
  simp only [Address.offset, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
private theorem byte_eval_address (env : Environment (ZMod p)) (cols : Var StoreByteChip.Columns (ZMod p)) :
    eval env cols.address_operation.addr_operation.value =
      (eval env cols).address_operation.addr_operation.value := by
  provable_struct_simp

omit [Fact (2 ^ 24 < p)] in
private theorem byte_eval_real (env : Environment (ZMod p)) (input : Var StoreByteChip.Inputs (ZMod p)) :
    Expression.eval env input.is_real = (eval env input).is_real := by
  rw [StoreByteChip.eval_inputs]
  simp only [circuit_norm]

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem byte_write_permitted_of_row {image : ProgramImage}
    (table : Table (ZMod p)) (physical : Array (ZMod p))
    (permission : ∀ gate address,
      (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
        table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw →
      Expression.eval (table.environment physical) gate = 1 →
      WritePermissionProvider.Permitted image (eval (table.environment physical) address))
    (component : table.component = (⟨ProtectedStore.byte⟩ : Component (ZMod p)))
    (active : ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreByteChip.rowView
      ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  intro write same
  change some _ = some write at same
  obtain rfl := Option.some.inj same
  apply Target.write_readOnly_false_of_permissions image _ (by change 1 ≤ 2 ^ 16; decide)
  intro index
  let input : Var StoreByteChip.Inputs (ZMod p) := varFromOffset StoreByteChip.Inputs 0
  let address := ((StoreByteChip.circuit input).output (size StoreByteChip.Inputs)).address_operation.addr_operation.value
  have zero : index.val = 0 := by have := index.isLt; change index.val < 1 at this; omega
  simp only [zero, Nat.cast_zero, Address.offset_zero]
  have permitted := permission
    input.is_real address (by
      rw [component, Component.interactionsWith_eq]
      change _ ∈ ((ProtectedStore.byte.main input).operations (size StoreByteChip.Inputs)).interactionsWith _
      rw [WritePermission.byte_emission]
      exact List.mem_singleton_self _)
    (by
      rw [byte_eval_real]
      have binding : eval (table.environment physical) input =
          (⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical) :=
        eval_varFromOffset_valueFromOffset StoreByteChip.Inputs 0 _
      rw [binding]
      exact active)
  rw [byte_eval_address] at permitted
  exact permitted

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem byte_write_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.allTables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (component : table.component = (⟨ProtectedStore.byte⟩ : Component (ZMod p)))
    (active : ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreByteChip.rowView
      ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreByteChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  exact byte_write_permitted_of_row table physical
    (row_pull_permitted witness constraints balanced table tableMem physical physicalMem) component active

omit [Fact (2 ^ 24 < p)] in
private theorem half_eval_address (env : Environment (ZMod p)) (cols : Var StoreHalfChip.Columns (ZMod p)) :
    eval env cols.address_operation.addr_operation.value =
      (eval env cols).address_operation.addr_operation.value := by
  provable_struct_simp

omit [Fact (2 ^ 24 < p)] in
private theorem half_eval_real (env : Environment (ZMod p)) (input : Var StoreHalfChip.Inputs (ZMod p)) :
    Expression.eval env input.is_real = (eval env input).is_real := by
  rw [StoreHalfChip.eval_inputs]
  simp only [circuit_norm]

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem half_write_permitted_of_row {image : ProgramImage}
    (table : Table (ZMod p)) (physical : Array (ZMod p))
    (permission : ∀ gate address,
      (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
        table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw →
      Expression.eval (table.environment physical) gate = 1 →
      WritePermissionProvider.Permitted image (eval (table.environment physical) address))
    (component : table.component = (⟨ProtectedStore.half⟩ : Component (ZMod p)))
    (active : ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreHalfChip.rowView
      ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  intro write same
  change some _ = some write at same
  obtain rfl := Option.some.inj same
  apply Target.write_readOnly_false_of_permissions image _ (by change 2 ≤ 2 ^ 16; decide)
  intro index
  let input : Var StoreHalfChip.Inputs (ZMod p) := varFromOffset StoreHalfChip.Inputs 0
  let address := ((StoreHalfChip.circuit input).output (size StoreHalfChip.Inputs)).address_operation.addr_operation.value
  have permitted := permission
    input.is_real (Address.offset address (.const (index.val : ZMod p))) (by
      rw [component, Component.interactionsWith_eq]
      change _ ∈ ((ProtectedStore.half.main input).operations (size StoreHalfChip.Inputs)).interactionsWith _
      rw [WritePermission.half_emission]
      exact List.mem_ofFn.mpr ⟨index, rfl⟩)
    (by
      rw [half_eval_real]
      have binding : eval (table.environment physical) input =
          (⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical) :=
        eval_varFromOffset_valueFromOffset StoreHalfChip.Inputs 0 _
      rw [binding]
      exact active)
  rw [eval_offset] at permitted
  rw [half_eval_address] at permitted
  exact permitted

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem half_write_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.allTables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (component : table.component = (⟨ProtectedStore.half⟩ : Component (ZMod p)))
    (active : ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreHalfChip.rowView
      ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreHalfChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  exact half_write_permitted_of_row table physical
    (row_pull_permitted witness constraints balanced table tableMem physical physicalMem) component active

omit [Fact (2 ^ 24 < p)] in
private theorem word_eval_address (env : Environment (ZMod p)) (cols : Var StoreWordChip.Columns (ZMod p)) :
    eval env cols.address_operation.addr_operation.value =
      (eval env cols).address_operation.addr_operation.value := by
  provable_struct_simp

omit [Fact (2 ^ 24 < p)] in
private theorem word_eval_real (env : Environment (ZMod p)) (input : Var StoreWordChip.Inputs (ZMod p)) :
    Expression.eval env input.is_real = (eval env input).is_real := by
  rw [StoreWordChip.eval_inputs]
  simp only [circuit_norm]

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem word_write_permitted_of_row {image : ProgramImage}
    (table : Table (ZMod p)) (physical : Array (ZMod p))
    (permission : ∀ gate address,
      (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
        table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw →
      Expression.eval (table.environment physical) gate = 1 →
      WritePermissionProvider.Permitted image (eval (table.environment physical) address))
    (component : table.component = (⟨ProtectedStore.word⟩ : Component (ZMod p)))
    (active : ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreWordChip.rowView
      ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  intro write same
  change some _ = some write at same
  obtain rfl := Option.some.inj same
  apply Target.write_readOnly_false_of_permissions image _ (by change 4 ≤ 2 ^ 16; decide)
  intro index
  let input : Var StoreWordChip.Inputs (ZMod p) := varFromOffset StoreWordChip.Inputs 0
  let address := ((StoreWordChip.circuit input).output (size StoreWordChip.Inputs)).address_operation.addr_operation.value
  have permitted := permission
    input.is_real (Address.offset address (.const (index.val : ZMod p))) (by
      rw [component, Component.interactionsWith_eq]
      change _ ∈ ((ProtectedStore.word.main input).operations (size StoreWordChip.Inputs)).interactionsWith _
      rw [WritePermission.word_emission]
      exact List.mem_ofFn.mpr ⟨index, rfl⟩)
    (by
      rw [word_eval_real]
      have binding : eval (table.environment physical) input =
          (⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical) :=
        eval_varFromOffset_valueFromOffset StoreWordChip.Inputs 0 _
      rw [binding]
      exact active)
  rw [eval_offset] at permitted
  rw [word_eval_address] at permitted
  exact permitted

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem word_write_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.allTables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (component : table.component = (⟨ProtectedStore.word⟩ : Component (ZMod p)))
    (active : ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreWordChip.rowView
      ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreWordChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  exact word_write_permitted_of_row table physical
    (row_pull_permitted witness constraints balanced table tableMem physical physicalMem) component active

omit [Fact (2 ^ 24 < p)] in
private theorem double_eval_address (env : Environment (ZMod p)) (cols : Var StoreDoubleChip.Columns (ZMod p)) :
    eval env cols.address_operation.addr_operation.value =
      (eval env cols).address_operation.addr_operation.value := by
  provable_struct_simp

omit [Fact (2 ^ 24 < p)] in
private theorem double_eval_real (env : Environment (ZMod p)) (input : Var StoreDoubleChip.Inputs (ZMod p)) :
    Expression.eval env input.is_real = (eval env input).is_real := by
  rw [StoreDoubleChip.eval_inputs]
  simp only [circuit_norm]

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem double_write_permitted_of_row {image : ProgramImage}
    (table : Table (ZMod p)) (physical : Array (ZMod p))
    (permission : ∀ gate address,
      (WritePermissionProvider.channel.pulledIf gate address).toRaw ∈
        table.component.operations.interactionsWith WritePermissionProvider.channel.toRaw →
      Expression.eval (table.environment physical) gate = 1 →
      WritePermissionProvider.Permitted image (eval (table.environment physical) address))
    (component : table.component = (⟨ProtectedStore.double⟩ : Component (ZMod p)))
    (active : ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreDoubleChip.rowView
      ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  intro write same
  change some _ = some write at same
  obtain rfl := Option.some.inj same
  apply Target.write_readOnly_false_of_permissions image _ (by change 8 ≤ 2 ^ 16; decide)
  intro index
  let input : Var StoreDoubleChip.Inputs (ZMod p) := varFromOffset StoreDoubleChip.Inputs 0
  let address := ((StoreDoubleChip.circuit input).output (size StoreDoubleChip.Inputs)).address_operation.addr_operation.value
  have permitted := permission
    input.is_real (Address.offset address (.const (index.val : ZMod p))) (by
      rw [component, Component.interactionsWith_eq]
      change _ ∈ ((ProtectedStore.double.main input).operations (size StoreDoubleChip.Inputs)).interactionsWith _
      rw [WritePermission.double_emission]
      exact List.mem_ofFn.mpr ⟨index, rfl⟩)
    (by
      rw [double_eval_real]
      have binding : eval (table.environment physical) input =
          (⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical) :=
        eval_varFromOffset_valueFromOffset StoreDoubleChip.Inputs 0 _
      rw [binding]
      exact active)
  rw [eval_offset] at permitted
  rw [double_eval_address] at permitted
  exact permitted

/-- Every byte of this active store's committed write is outside the fixed ROM. -/
theorem double_write_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (table : Table (ZMod p)) (tableMem : table ∈ witness.allTables)
    (physical : Array (ZMod p)) (physicalMem : physical ∈ table.table)
    (component : table.component = (⟨ProtectedStore.double⟩ : Component (ZMod p)))
    (active : ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical)).is_real = 1) :
    Target.RowWritePermitted image (StoreDoubleChip.rowView
      ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowInput (table.environment physical))
      ((⟨StoreDoubleChip.circuit⟩ : Component (ZMod p)).rowOutput (table.environment physical))) := by
  exact double_write_permitted_of_row table physical
    (row_pull_permitted witness constraints balanced table tableMem physical physicalMem) component active

end SP1Clean.Soundness.ProtectedLocalCore
