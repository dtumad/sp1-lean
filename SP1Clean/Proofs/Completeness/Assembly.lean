import SP1Clean.FormalModel.TraceGen.InstructionRegistry
import SP1Clean.Proofs.Completeness.Providers
import SP1Clean.Soundness.EnsembleChannels
import SP1Clean.Soundness.EnsembleLookups
import SP1Clean.FormalModel.TraceGen.Bump
import SP1Clean.Proofs.Chips.SyscallInstrsChip.Witgen
import SP1Clean.Proofs.Chips.AddChip.Complete
import SP1Clean.Proofs.Chips.AddiChip.Complete
import SP1Clean.Proofs.Chips.AddwChip.Complete
import SP1Clean.Proofs.Chips.SubChip.Complete
import SP1Clean.Proofs.Chips.SubwChip.Complete
import SP1Clean.Proofs.Chips.BitwiseChip.Complete
import SP1Clean.Proofs.Chips.LtChip.Complete
import SP1Clean.Proofs.Chips.ShiftLeftChip.Complete
import SP1Clean.Proofs.Chips.ShiftRightChip.Complete
import SP1Clean.Proofs.Chips.JalChip.Complete
import SP1Clean.Proofs.Chips.JalrChip.Complete
import SP1Clean.Proofs.Chips.BranchChip.Complete
import SP1Clean.Proofs.Chips.UTypeChip.Complete
import SP1Clean.Proofs.Chips.LoadByteChip.Complete
import SP1Clean.Proofs.Chips.LoadHalfChip.Complete
import SP1Clean.Proofs.Chips.LoadWordChip.Complete
import SP1Clean.Proofs.Chips.LoadDoubleChip.Complete
import SP1Clean.Proofs.Chips.LoadX0Chip.Complete
import SP1Clean.Proofs.Chips.StoreByteChip.Complete
import SP1Clean.Proofs.Chips.StoreHalfChip.Complete
import SP1Clean.Proofs.Chips.StoreWordChip.Complete
import SP1Clean.Proofs.Chips.StoreDoubleChip.Complete
import SP1Clean.Proofs.Chips.MulChip.Complete
import SP1Clean.Proofs.Chips.DivRemChip.Complete
import SP1Clean.Proofs.Chips.AluX0Chip.Complete
import ToClean.Air.EnsembleBuild

/-! # Assembling a shard's physical AIR witness

The semantic trace selects events for 25 instruction tables and occurrences for 30 provider
and boundary tables. Their completeness theorems build the 55 physical tables in the ensemble's
registry order. Clean derives committed prover data from those tables; `generationData` and
`hint` are inputs to row generation, not an independently supplied commitment.

The inventory's constraints depend only on row cells and fixed lookups, so they hold at the
canonical committed data even when it differs from the generation input. Channel guarantees,
program bindings and agreement with a Sail execution remain separate obligations.

Instruction traces are unpadded; power-of-two padding of active tables remains a separate
obligation. Provider multiplicities remain explicit, preserving repeated keys, zero-count entries
and boolean memory selectors. The trace record lives beside the completeness proofs because its
provider occurrence types depend on chip input types.
-/

/-! ## Completeness-side realizations of the neutral table identities

The Model-layer identity modules intentionally know nothing about trace-generation records.  This
higher layer supplies the dependent payload and validity families used by the generated witness.
-/

namespace SP1Clean.ProviderTableId

open SP1Clean.TraceGen

/-- Semantic occurrence type routed to one provider, boundary, or bump table. Reducible so a
`List id.Occurrence` is the concrete entry list at implicit transparency, where the closure
proofs' rewrites identify the two. -/
@[reducible] def Occurrence : ProviderTableId → Type
  | .byte _ => ByteEntry
  | .range _ => RangeEntry
  | .program => RomEntry
  | .memoryInit => MemRecordEntry
  | .memoryFinalize => MemRecordEntry
  | .memoryBump => MemoryBumpEvent
  | .stateBump => StateBumpEvent
  -- The deterministic compiler emits no real halt rows yet; `Empty` makes that type-level (the
  -- 2.4b tranche replaces it with the semantic halt event). The halt table itself is never empty:
  -- `HaltChip.haltTraceInputs [] = [paddingInputs]`, whose `⟨0⟩` Exit push balances the verifier.
  | .halt => Empty
  -- The compiler emits no syscall rows yet either, but for a different reason than `halt`: the
  -- syscall table is genuinely *empty* rather than one padding row, because its Exit push is
  -- positively gated and needs no anti-gated companion to balance the verifier.
  | .syscallInstrs => Empty

/-- Side condition required by one provider table's trace builder. -/
def Valid : (id : ProviderTableId) → id.Occurrence → Prop
  | .byte _, e => e.WellFormed
  | .range width, e => e.WellFormed width.val
  | .program, e => e.WellFormed
  | .memoryInit, e => e.WellFormedInit
  | .memoryFinalize, _ => True
  | .memoryBump, e => e.WellFormed
  | .stateBump, e => e.WellFormed
  | .halt, e => e.elim
  | .syscallInstrs, e => e.elim

end SP1Clean.ProviderTableId

namespace SP1Clean.Soundness

open Circuit
open Air.Flat (Component Table EnsembleWitness)
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance traceAssemblyFieldBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## The generated trace -/

/-- Semantic events and provider occurrences routed by the ensemble's two registries.
`generationData` and `hint` feed the table builders. `boundary` is the public verifier input;
committed data is derived from the resulting physical tables by `SupportedCoreTraceWitness.data`.
Whether these events form a Sail execution is stated separately by the completeness relation. -/
structure SupportedCoreTraceWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] where
  instructionEvents : (id : InstructionChipId) → List id.Event
  providerOccurrences : (id : ProviderTableId) → List id.Occurrence
  /-- Physical instruction rows are representable by Clean's row index. -/
  instructionCapacity : ∀ id, (instructionEvents id).length ≤ UInt64.size
  /-- Physical provider occurrences are representable by Clean's row index. -/
  providerCapacity : ∀ id, (providerOccurrences id).length ≤ UInt64.size
  /-- Prover data supplied to the circuit witness builders. -/
  generationData : ProverData (ZMod p)
  hint : ProverHint (ZMod p)
  boundary : SP1PublicIO (ZMod p)

namespace SupportedCoreTraceWitness

variable (trace : SupportedCoreTraceWitness p)

/--
**A generated trace is well-formed** when every event or occurrence it emits satisfies the side
condition selected by the same registry identity — the exact premise of that table's
`traceTable_constraints` theorem.

Nothing here is a range fact about a *witnessed* cell: those are the circuits' own business, and
witness generation supplies them. What a generator owes is that the semantic content it routed to
a table belongs there — an `AND` event to the bitwise chip, an aligned address to the word-load
chip, a byte-sized operand pair to a byte provider.
-/
structure WellFormed : Prop where
  instruction : ∀ id e, e ∈ trace.instructionEvents id → id.Valid e
  provider : ∀ id e, e ∈ trace.providerOccurrences id → id.Valid e
  boundary : trace.boundary.LimbBounds

/-! ## The 55 tables -/

/-- The shard's public boundary row, stored exactly as the verifier reads it. -/
def publicValues : SP1PublicIO (ZMod p) := trace.boundary

/-- Semantic input rows indexed by the same registry that owns each physical circuit. -/
def instructionInputsFor : (id : InstructionChipId) → List ((supportedChipFor (p := p) id).table.Input (ZMod p))
  | .add => AddChip.traceInputs (trace.instructionEvents .add) 0
  | .addi => AddiChip.traceInputs (trace.instructionEvents .addi) 0
  | .addw => AddwChip.traceInputs (trace.instructionEvents .addw) 0
  | .sub => SubChip.traceInputs (trace.instructionEvents .sub) 0
  | .subw => SubwChip.traceInputs (trace.instructionEvents .subw) 0
  | .bitwise => BitwiseChip.traceInputs (trace.instructionEvents .bitwise) 0
  | .lt => LtChip.traceInputs (trace.instructionEvents .lt) 0
  | .shiftLeft => ShiftLeftChip.traceInputs (trace.instructionEvents .shiftLeft) 0
  | .shiftRight => ShiftRightChip.traceInputs (trace.instructionEvents .shiftRight) 0
  | .jal => JalChip.traceInputs (trace.instructionEvents .jal) 0
  | .jalr => JalrChip.traceInputs (trace.instructionEvents .jalr) 0
  | .branch => BranchChip.traceInputs (trace.instructionEvents .branch) 0
  | .uType => UTypeChip.traceInputs (trace.instructionEvents .uType) 0
  | .loadByte => LoadByteChip.traceInputs (trace.instructionEvents .loadByte)
  | .loadHalf => LoadHalfChip.traceInputs (trace.instructionEvents .loadHalf)
  | .loadWord => LoadWordChip.traceInputs (trace.instructionEvents .loadWord)
  | .loadDouble => LoadDoubleChip.traceInputs (trace.instructionEvents .loadDouble)
  | .loadX0 => LoadX0Chip.traceInputs (trace.instructionEvents .loadX0)
  | .storeByte => StoreByteChip.traceInputs (trace.instructionEvents .storeByte)
  | .storeHalf => StoreHalfChip.traceInputs (trace.instructionEvents .storeHalf)
  | .storeWord => StoreWordChip.traceInputs (trace.instructionEvents .storeWord)
  | .storeDouble => StoreDoubleChip.traceInputs (trace.instructionEvents .storeDouble)
  | .mul => MulChip.traceInputs (trace.instructionEvents .mul) 0
  | .divRem => DivRemChip.traceInputs (trace.instructionEvents .divRem) 0
  | .aluX0 => AluX0Chip.traceInputs (trace.instructionEvents .aluX0) 0

/-- An instruction bucket contributes exactly one physical input per semantic event. -/
theorem instructionInputsFor_length (id : InstructionChipId) :
    (trace.instructionInputsFor id).length = (trace.instructionEvents id).length := by
  cases id with
  | add =>
      change (AddChip.traceInputs (p := p) (trace.instructionEvents .add) 0).length = _
      simp only [AddChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | addi =>
      change (AddiChip.traceInputs (p := p) (trace.instructionEvents .addi) 0).length = _
      simp only [AddiChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | addw =>
      change (AddwChip.traceInputs (p := p) (trace.instructionEvents .addw) 0).length = _
      simp only [AddwChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | sub =>
      change (SubChip.traceInputs (p := p) (trace.instructionEvents .sub) 0).length = _
      simp only [SubChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | subw =>
      change (SubwChip.traceInputs (p := p) (trace.instructionEvents .subw) 0).length = _
      simp only [SubwChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | bitwise =>
      change (BitwiseChip.traceInputs (p := p) (trace.instructionEvents .bitwise) 0).length = _
      simp only [BitwiseChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | lt =>
      change (LtChip.traceInputs (p := p) (trace.instructionEvents .lt) 0).length = _
      simp only [LtChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | shiftLeft =>
      change (ShiftLeftChip.traceInputs (p := p) (trace.instructionEvents .shiftLeft) 0).length = _
      simp only [ShiftLeftChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | shiftRight =>
      change (ShiftRightChip.traceInputs (p := p) (trace.instructionEvents .shiftRight) 0).length = _
      simp only [ShiftRightChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | jal =>
      change (JalChip.traceInputs (p := p) (trace.instructionEvents .jal) 0).length = _
      simp only [JalChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | jalr =>
      change (JalrChip.traceInputs (p := p) (trace.instructionEvents .jalr) 0).length = _
      simp only [JalrChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | branch =>
      change (BranchChip.traceInputs (p := p) (trace.instructionEvents .branch) 0).length = _
      simp only [BranchChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | uType =>
      change (UTypeChip.traceInputs (p := p) (trace.instructionEvents .uType) 0).length = _
      simp only [UTypeChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | loadByte => exact List.length_map ..
  | loadHalf => exact List.length_map ..
  | loadWord => exact List.length_map ..
  | loadDouble => exact List.length_map ..
  | loadX0 => exact List.length_map ..
  | storeByte => exact List.length_map ..
  | storeHalf => exact List.length_map ..
  | storeWord => exact List.length_map ..
  | storeDouble => exact List.length_map ..
  | mul =>
      change (MulChip.traceInputs (p := p) (trace.instructionEvents .mul) 0).length = _
      simp only [MulChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | divRem =>
      change (DivRemChip.traceInputs (p := p) (trace.instructionEvents .divRem) 0).length = _
      simp only [DivRemChip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..
  | aluX0 =>
      change (AluX0Chip.traceInputs (p := p) (trace.instructionEvents .aluX0) 0).length = _
      simp only [AluX0Chip.traceInputs, List.length_append, List.length_replicate, Nat.add_zero]
      exact List.length_map ..

/-- Input representability follows from the exact semantic occurrence bound. -/
theorem instructionInputsFor_capacity (id : InstructionChipId) :
    (trace.instructionInputsFor id).length ≤ UInt64.size := by
  rw [instructionInputsFor_length]
  exact trace.instructionCapacity id

/-- Pure arithmetic builders ignore the shared hint; the remaining builders use it. -/
def instructionHintFor : InstructionChipId → ProverHint (ZMod p)
  | .bitwise | .lt | .shiftLeft | .shiftRight | .branch | .mul | .divRem => ProverHint.empty _
  | _ => trace.hint

/-- Build each instruction table through the circuit-bearing registry and its indexed inputs. -/
def instructionTableFor (id : InstructionChipId) : Table (ZMod p) :=
  Table.build (supportedChipFor id).table (trace.instructionInputsFor id)
    trace.generationData (trace.instructionHintFor id) (trace.instructionInputsFor_capacity id)
    (by cases id <;> trivial)

/-- The twenty-five built instruction tables, in the one physical order fixed by the neutral
instruction registry. -/
def instructionTables : List (Table (ZMod p)) :=
  InstructionChipId.all.map trace.instructionTableFor

/-- Pointwise positional agreement between the completeness builder and the circuit-bearing
supported-machine registry. -/
@[simp] theorem instructionTableFor_component (id : InstructionChipId) :
    (trace.instructionTableFor id).component = (supportedChipFor (p := p) id).table := rfl

/-- Pointwise instruction-table completeness.  This is the sole proof that dispatches on all
twenty-five instruction identities; list-level assembly below only reasons through `List.map`. -/
theorem instructionTableFor_constraints (wf : trace.WellFormed) (id : InstructionChipId) :
    (trace.instructionTableFor id).Constraints := by
  cases id with
  | add =>
    exact AddChip.traceTable_constraints _ _ _ _ (wf.instruction .add)
      (trace.instructionInputsFor_capacity .add)
  | addi =>
    exact AddiChip.traceTable_constraints _ _ _ _ (wf.instruction .addi)
      (trace.instructionInputsFor_capacity .addi)
  | addw =>
    exact AddwChip.traceTable_constraints _ _ _ _ (wf.instruction .addw)
      (trace.instructionInputsFor_capacity .addw)
  | sub =>
    exact SubChip.traceTable_constraints _ _ _ _ (wf.instruction .sub)
      (trace.instructionInputsFor_capacity .sub)
  | subw =>
    exact SubwChip.traceTable_constraints _ _ _ _ (wf.instruction .subw)
      (trace.instructionInputsFor_capacity .subw)
  | bitwise =>
    exact BitwiseChip.traceTable_constraints _ _ _ (wf.instruction .bitwise)
      (trace.instructionInputsFor_capacity .bitwise)
  | lt =>
    exact LtChip.traceTable_constraints _ _ _ (wf.instruction .lt)
      (trace.instructionInputsFor_capacity .lt)
  | shiftLeft =>
    exact ShiftLeftChip.traceTable_constraints _ _ _ (wf.instruction .shiftLeft)
      (trace.instructionInputsFor_capacity .shiftLeft)
  | shiftRight =>
    exact ShiftRightChip.traceTable_constraints _ _ _ (wf.instruction .shiftRight)
      (trace.instructionInputsFor_capacity .shiftRight)
  | jal =>
    exact JalChip.traceTable_constraints _ _ _ _ (wf.instruction .jal)
      (trace.instructionInputsFor_capacity .jal)
  | jalr =>
    exact JalrChip.traceTable_constraints _ _ _ _ (wf.instruction .jalr)
      (trace.instructionInputsFor_capacity .jalr)
  | branch =>
    exact BranchChip.traceTable_constraints _ _ _ (wf.instruction .branch)
      (trace.instructionInputsFor_capacity .branch)
  | uType =>
    exact UTypeChip.traceTable_constraints _ _ _ _ (wf.instruction .uType)
      (trace.instructionInputsFor_capacity .uType)
  | loadByte =>
    exact LoadByteChip.traceTable_constraints _ _ _ (wf.instruction .loadByte)
      (trace.instructionInputsFor_capacity .loadByte)
  | loadHalf =>
    exact LoadHalfChip.traceTable_constraints _ _ _ (wf.instruction .loadHalf)
      (trace.instructionInputsFor_capacity .loadHalf)
  | loadWord =>
    exact LoadWordChip.traceTable_constraints _ _ _ (wf.instruction .loadWord)
      (trace.instructionInputsFor_capacity .loadWord)
  | loadDouble =>
    exact LoadDoubleChip.traceTable_constraints _ _ _ (wf.instruction .loadDouble)
      (trace.instructionInputsFor_capacity .loadDouble)
  | loadX0 =>
    exact LoadX0Chip.traceTable_constraints _ _ _ (wf.instruction .loadX0)
      (trace.instructionInputsFor_capacity .loadX0)
  | storeByte =>
    exact StoreByteChip.traceTable_constraints _ _ _ (wf.instruction .storeByte)
      (trace.instructionInputsFor_capacity .storeByte)
  | storeHalf =>
    exact StoreHalfChip.traceTable_constraints _ _ _ (wf.instruction .storeHalf)
      (trace.instructionInputsFor_capacity .storeHalf)
  | storeWord =>
    exact StoreWordChip.traceTable_constraints _ _ _ (wf.instruction .storeWord)
      (trace.instructionInputsFor_capacity .storeWord)
  | storeDouble =>
    exact StoreDoubleChip.traceTable_constraints _ _ _ (wf.instruction .storeDouble)
      (trace.instructionInputsFor_capacity .storeDouble)
  | mul =>
    exact MulChip.traceTable_constraints _ _ _ (wf.instruction .mul)
      (trace.instructionInputsFor_capacity .mul)
  | divRem =>
    exact DivRemChip.traceTable_constraints _ _ _ (wf.instruction .divRem)
      (trace.instructionInputsFor_capacity .divRem)
  | aluX0 =>
    exact AluX0Chip.traceTable_constraints _ _ _ _ (wf.instruction .aluX0)
      (trace.instructionInputsFor_capacity .aluX0)

/-- The completeness registry projects to the soundness registry component for component. -/
theorem instructionTables_map_component :
    trace.instructionTables.map (·.component) = sp1Tables := by
  simp only [instructionTables, sp1Tables, supportedChips, List.map_map]
  exact List.map_congr_left fun id _ => trace.instructionTableFor_component id

/-- Constraint completeness lifted pointwise through the instruction registry. -/
theorem instructionTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.instructionTables, table.Constraints := by
  intro table tableMem
  rw [instructionTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.instructionTableFor_constraints wf id

/-- Provider inputs use the same identities as the soundness component registry. -/
def providerInputsFor : (id : ProviderTableId) →
    List ((Soundness.providerTableFor (p := p) id).Input (ZMod p))
  | .byte .u8Range => ByteChip.U8Range.traceInputs (trace.providerOccurrences (.byte .u8Range))
  | .byte .msb => ByteChip.MSB.traceInputs (trace.providerOccurrences (.byte .msb))
  | .byte .andByte => ByteChip.AndByte.traceInputs (trace.providerOccurrences (.byte .andByte))
  | .byte .orByte => ByteChip.OrByte.traceInputs (trace.providerOccurrences (.byte .orByte))
  | .byte .xorByte => ByteChip.XorByte.traceInputs (trace.providerOccurrences (.byte .xorByte))
  | .byte .ltu => ByteChip.Ltu.traceInputs (trace.providerOccurrences (.byte .ltu))
  | .range width => RangeChip.traceInputs (trace.providerOccurrences (.range width))
  | .program => ProgramProviderChip.traceInputs (trace.providerOccurrences .program)
  | .memoryInit => MemoryProviderChip.traceInputs (trace.providerOccurrences .memoryInit)
  | .memoryFinalize => MemoryFinalizeChip.traceInputs (trace.providerOccurrences .memoryFinalize)
  | .memoryBump => memoryBumpTraceInputs (trace.providerOccurrences .memoryBump)
  | .stateBump => stateBumpTraceInputs (trace.providerOccurrences .stateBump)
  | .halt => HaltChip.haltTraceInputs (trace.providerOccurrences .halt)
  | .syscallInstrs => SyscallInstrsChip.syscallInstrsTraceInputs (trace.providerOccurrences .syscallInstrs)

/-- Provider height includes the ordinary compiler's one Halt padding row and empty syscall table. -/
def providerHeight (id : ProviderTableId) : ℕ :=
  match id with
  | .halt => 1
  | .syscallInstrs => 0
  | _ => (trace.providerOccurrences id).length

/-- Input generation preserves occurrence counts, with the two explicit system-table shapes. -/
theorem providerInputsFor_length (id : ProviderTableId) :
    (trace.providerInputsFor id).length = trace.providerHeight id := by
  cases id with
  | byte provider => cases provider <;> exact List.length_map ..
  | range width => exact List.length_map ..
  | program => exact List.length_map ..
  | memoryInit => exact List.length_map ..
  | memoryFinalize => exact List.length_map ..
  | memoryBump => exact List.length_map ..
  | stateBump => exact List.length_map ..
  | halt =>
      change (HaltChip.haltTraceInputs (p := p) (trace.providerOccurrences .halt)).length = 1
      cases trace.providerOccurrences .halt with
      | nil => rfl
      | cons event _ => exact event.elim
  | syscallInstrs => rfl

/-- Occurrence capacity includes the fixed Halt padding row and empty syscall input. -/
theorem providerInputsFor_capacity (id : ProviderTableId) :
    (trace.providerInputsFor id).length ≤ UInt64.size := by
  rw [providerInputsFor_length]
  cases id <;> first
    | exact trace.providerCapacity _
    | exact Nat.zero_le _
    | exact Nat.le_of_lt (by decide : 1 < UInt64.size)

/-- Build a provider or boundary table through its registered circuit and semantic inputs. -/
def providerTableFor (id : ProviderTableId) : Table (ZMod p) :=
  Table.build (Soundness.providerTableFor id) (trace.providerInputsFor id)
    trace.generationData trace.hint (trace.providerInputsFor_capacity id)
    (by cases id with
      | byte provider => cases provider <;> trivial
      | range _ | program | memoryInit | memoryFinalize | memoryBump | stateBump | halt | syscallInstrs => trivial)

/-- The range-provider segment in physical registry order. -/
def rangeTables : List (Table (ZMod p)) :=
  RangeChip.allWidths.map fun width => trace.providerTableFor (.range width)

/-- The thirty built provider and boundary tables, in the one physical order fixed by the
neutral provider registry. -/
def providerTables : List (Table (ZMod p)) :=
  ProviderTableId.all.map trace.providerTableFor

/-- Pointwise positional agreement between the completeness provider builder and the
circuit-bearing soundness registry. -/
@[simp] theorem providerTableFor_component (id : ProviderTableId) :
    (trace.providerTableFor id).component = Soundness.providerTableFor (p := p) id := rfl

/-- Pointwise provider-table completeness. This is the sole proof that dispatches on all provider
identities; list-level assembly below only reasons through `List.map`. -/
theorem providerTableFor_constraints (wf : trace.WellFormed) (id : ProviderTableId) :
    (trace.providerTableFor id).Constraints := by
  cases id with
  | byte provider =>
      cases provider with
      | u8Range =>
          exact ByteChip.U8Range.traceTable_constraints _ _ _
            (wf.provider (.byte .u8Range)) (trace.providerInputsFor_capacity (.byte .u8Range))
      | msb => exact ByteChip.MSB.traceTable_constraints _ _ _ (wf.provider (.byte .msb)) (trace.providerInputsFor_capacity (.byte .msb))
      | andByte =>
          exact ByteChip.AndByte.traceTable_constraints _ _ _
            (wf.provider (.byte .andByte)) (trace.providerInputsFor_capacity (.byte .andByte))
      | orByte =>
          exact ByteChip.OrByte.traceTable_constraints _ _ _ (wf.provider (.byte .orByte)) (trace.providerInputsFor_capacity (.byte .orByte))
      | xorByte =>
          exact ByteChip.XorByte.traceTable_constraints _ _ _
            (wf.provider (.byte .xorByte)) (trace.providerInputsFor_capacity (.byte .xorByte))
      | ltu => exact ByteChip.Ltu.traceTable_constraints _ _ _ (wf.provider (.byte .ltu)) (trace.providerInputsFor_capacity (.byte .ltu))
  | range width =>
      exact RangeChip.traceTable_constraints _ (Nat.le_of_lt_succ width.isLt) _ _ _
        (wf.provider (.range width)) (trace.providerInputsFor_capacity (.range width))
  | program =>
      exact ProgramProviderChip.traceTable_constraints _ _ _ (wf.provider .program) (trace.providerInputsFor_capacity .program)
  | memoryInit =>
      exact MemoryProviderChip.traceTable_constraints _ _ _ (wf.provider .memoryInit) (trace.providerInputsFor_capacity .memoryInit)
  | memoryFinalize => exact MemoryFinalizeChip.traceTable_constraints _ _ _ (trace.providerInputsFor_capacity .memoryFinalize)
  | memoryBump =>
      exact MemoryBumpChip.traceTable_constraints _ _ _
        (memoryBumpTraceInputs_spec (wf.provider .memoryBump)) (trace.providerInputsFor_capacity .memoryBump)
  | stateBump =>
      exact StateBumpChip.traceTable_constraints _ _ _
        (stateBumpTraceInputs_spec (wf.provider .stateBump)) (trace.providerInputsFor_capacity .stateBump)
  | halt =>
      exact HaltChip.traceTable_constraints _ _ _
        (HaltChip.haltTraceInputs_spec (trace.providerOccurrences .halt)) (trace.providerInputsFor_capacity .halt)
  | syscallInstrs =>
      exact SyscallInstrsChip.traceTable_constraints (trace.providerOccurrences .syscallInstrs) _ _

/-- The full 55-table assembly is the instruction registry followed by the provider segment. -/
def tables : List (Table (ZMod p)) :=
  trace.instructionTables ++ trace.providerTables

/-- Committed data is derived from complete physical table inputs, using Clean's canonical map. -/
def data : ProverData (ZMod p) := Air.Flat.deriveProverData trace.tables

/-- The provider segment projects to the ensemble's provider components in physical order. -/
theorem providerTables_map_component :
    trace.providerTables.map (·.component) = sp1ProviderTables := by
  simp only [providerTables, sp1ProviderTables, List.map_map]
  exact List.map_congr_left fun id _ => trace.providerTableFor_component id

/-- Every well-formed provider occurrence segment builds constraint-satisfying tables. -/
theorem providerTables_constraints (wf : trace.WellFormed) :
    ∀ table ∈ trace.providerTables, table.Constraints := by
  intro table tableMem
  rw [providerTables] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact trace.providerTableFor_constraints wf id

/-- **The assembled tables are the ensemble's tables**, component for component and in order. One
`rfl`: every completeness-side `component` is by definition the wrapper `sp1Tables` /
`sp1ProviderTables` build, and `Table.build` record the component they were
given. -/
theorem tables_map_component :
    (trace.tables.map (·.component)) = (sp1Ensemble (p := p)).tables := by
  rw [tables, List.map_append, instructionTables_map_component,
    providerTables_map_component, sp1Ensemble_tables]

/-! ## The assembled witness -/

/-- The physical tables in registry order and the public verifier input. -/
def witness : EnsembleWitness (sp1Ensemble (p := p)) :=
  EnsembleWitness.ofTables _ trace.tables trace.publicValues trace.tables_map_component

@[simp] theorem witness_publicInput : trace.witness.publicInput = trace.publicValues := rfl
@[simp] theorem witness_data : trace.witness.data = trace.data :=
  EnsembleWitness.ofTables_data _ _ _ _
@[simp] theorem witness_tables :
    trace.witness.tables = Air.Flat.withDerivedData trace.tables := rfl

/-! ## Constraints -/

/-- **The compiler's syscall table has no rows**, in the positional shape the two non-core buses'
silence lemmas ask for. `syscallInstrsTraceInputs` is `[]` by construction (`List Empty` in, empty
list out), so this is a property of *this compiler's trace* rather than of the chip — the chip
genuinely speaks on seven buses. It is exactly what stops holding when the compiler learns to emit
syscall rows. -/
theorem witness_syscallTable_nil :
    ∀ t : Air.Flat.Table (ZMod p),
      trace.witness.tables[syscallTablePosition]? = some t → t.table = [] := by
  intro t ht
  have hpos : trace.witness.tables[syscallTablePosition]?
      = some { trace.providerTableFor .syscallInstrs with data := trace.data } := rfl
  rw [hpos] at ht
  rw [← Option.some.inj ht]
  rfl

/-- Every generated row satisfies the physical constraints at the data derived from all tables.
The public verifier's assertions are channel obligations, proved separately from this theorem. -/
theorem witness_constraints (wf : trace.WellFormed) : trace.witness.Constraints := by
  intro table member row rowMem
  have componentMem :=
    EnsembleWitness.component_mem_tables_of_mem (witness := trace.witness) member
  rw [witness_tables, Air.Flat.withDerivedData] at member
  obtain ⟨built, builtMem, rfl⟩ := List.mem_map.mp member
  apply sp1Table_constraints_setData built.component componentMem (data := built.data)
  rw [tables] at builtMem
  rcases List.mem_append.mp builtMem with instructionMem | providerMem
  · exact trace.instructionTables_constraints wf built instructionMem row rowMem
  · exact trace.providerTables_constraints wf built providerMem row rowMem

end SupportedCoreTraceWitness

end SP1Clean.Soundness
