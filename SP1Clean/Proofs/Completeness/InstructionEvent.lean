import SP1Clean.Semantics.Transition.TransitionView
import SP1Clean.Semantics.Transition.AccessSchedule
import SP1Clean.Semantics.Execution.ExecutionEncoding
import SP1Clean.Proofs.Completeness.InstructionPredecessors

/-!
# One-transition instruction-event compilation

This module is the proof-independent bridge from one decoded, supported Sail transition to the
semantic event consumed by exactly one of the twenty-five native instruction tables.  It does not
build a Clean row and it does not inspect a chip circuit.  Instead it combines three canonical
projections:

* `instructionRouteId` selects the registry identity;
* `instructionAccessPlan?` reads the source/target values in SP1's `RAM,C,B,A` role order; and
* the canonical global access scheduler supplies displaced timestamps after any required
  24-bit-window register refresh.

The resulting `RoutedEvent` is therefore registry-indexed by construction.  `InstructionEventReady`
is intentionally just successful execution of this transparent extractor.  In particular it does
not contain `InstructionChipId.Valid` (or an existential table witness) as a premise.  Address-space,
alignment, and control-flow-target facts needed for full per-chip validity remain semantic facts of
the official Sail step and can be proved at the later execution-fold boundary.
-/

open LeanRV64D

namespace SP1Clean.TraceGen

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Semantics
open SP1Clean.Soundness.Target

/-! ## Small family-neutral projections -/

/-- Preserve the decoded immediate width: branches use thirteen bits, while I-type and memory
operands use twelve. Narrowing before sign extension changes valid branch targets. -/
private def sextNat {width : ℕ} (immediate : BitVec width) : ℕ :=
  (immediate.signExtend 64).toNat

private def utypeImmediateNat (immediate : BitVec 20) : ℕ :=
  ((immediate.signExtend 64) <<< 12).toNat

/-- The bit-vector projection used by the compiler is exactly the executor-side natural-number
encoding required by `JTypeEvent.UTypeImm`. -/
theorem utypeImmediateNat_eq_luiImmNat (immediate : BitVec 20) :
    utypeImmediateNat immediate = luiImmNat immediate.toNat := by
  have immediateLt : immediate.toNat < 2 ^ 20 := immediate.isLt
  have msb_iff : immediate.msb = true ↔ 2 ^ 19 ≤ immediate.toNat := by
    rw [BitVec.msb_eq_decide, decide_eq_true_eq]
  unfold utypeImmediateNat luiImmNat
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : immediate.toNat < 2 ^ 64)]
  by_cases sign : immediate.msb = true
  · have highGe := msb_iff.mp sign
    have high : ¬ immediate.toNat < 2 ^ 19 := by omega
    rw [ite_eq_left sign, ite_eq_right high]
    have residueLt : immediate.toNat * 4096 + (2 ^ 64 - 2 ^ 32) < 2 ^ 64 := by
      omega
    have rearrange :
        (immediate.toNat + (2 ^ 64 - 2 ^ 20)) * 2 ^ 12 =
          (2 ^ 64) * 4095 + (immediate.toNat * 4096 + (2 ^ 64 - 2 ^ 32)) := by
      omega
    rw [rearrange, Nat.add_mod, Nat.mul_mod]
    simp only [Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
      Nat.mod_eq_of_lt residueLt]
  · have low : immediate.toNat < 2 ^ 19 := by
      by_contra high
      exact sign (msb_iff.mpr (by omega))
    rw [ite_eq_right sign, ite_eq_left low]
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt]
    omega

/-! ## Adapter-family event constructors -/

/-- Extract the register indices of a C/B/A-shaped instruction. -/
private def cbaRegisters? : instruction → Option (BitVec 5 × BitVec 5 × BitVec 5)
  | .RTYPE (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .RTYPEW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .MUL (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .MULW (rs2, rs1, rd) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .DIV (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .DIVW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .REM (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .REMW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | _ => none

/-- Build an R-type family event from the canonical C/B/A stamped shape. -/
private def rTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option RTypeEvent := do
  let registers ← cbaRegisters? decoded
  match stamped with
  | [c, b, a] =>
      match c.touch.slot, b.touch.slot, a.touch.slot with
      | .opC, .opB, .opA =>
          pure
            { clk := clk
              pc := pc
              opcode := opcode
              opA := registers.2.2.toNat
              opB := registers.2.1.toNat
              opC := registers.1.toNat
              b := b.touch.pulled.toNat
              c := c.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := c.previous }
      | _, _, _ => none
  | _ => none

/-- Build the register-register form of the ALU-type family. -/
private def aluRegisterEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ALUTypeEvent := do
  let registers ← cbaRegisters? decoded
  match stamped with
  | [c, b, a] =>
      match c.touch.slot, b.touch.slot, a.touch.slot with
      | .opC, .opB, .opA =>
          pure
            { clk := clk
              pc := pc
              opcode := opcode
              opA := registers.2.2.toNat
              opB := registers.2.1.toNat
              opC := registers.1.toNat
              immC := 0
              b := b.touch.pulled.toNat
              c := c.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := c.previous }
      | _, _, _ => none
  | _ => none

/-- Build the immediate-C form of the ALU-type family. -/
private def aluImmediateEventOf? (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec 64) : Option ALUTypeEvent :=
  match stamped with
  | [b, a] =>
      match b.touch.slot, a.touch.slot with
      | .opB, .opA =>
          some
            { clk := clk
              pc := pc
              opcode := opcode
              opA := (regidxBits rd).toNat
              opB := (regidxBits rs1).toNat
              opC := immediate.toNat
              immC := 1
              b := b.touch.pulled.toNat
              c := 0
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := 0 }
      | _, _ => none
  | _ => none

/-- Build whichever ALU-type shape the decoded instruction carries. -/
private def aluTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ALUTypeEvent :=
  match decoded with
  | .ITYPE (imm, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (imm.signExtend 64)
  | .SHIFTIOP (shamt, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (shamt.setWidth 64)
  | .SHIFTIWOP (shamt, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (shamt.setWidth 64)
  | .ADDIW (imm, rs1, rd) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (imm.signExtend 64)
  | other => aluRegisterEvent? other stamped clk pc opcode

/-- Preserve the decoded immediate width on the two-register I/branch adapter. -/
private def iOperands? {width : ℕ} (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec width) : Option ITypeEvent :=
  match stamped with
  | [b, a] =>
      match b.touch.slot, a.touch.slot with
      | .opB, .opA =>
          some
            { clk := clk
              pc := pc
              opcode := opcode
              opA := (regidxBits rd).toNat
              opB := (regidxBits rs1).toNat
              imm := sextNat immediate
              b := b.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous }
      | _, _ => none
  | _ => none

/-- Build the shared I-type record in its ADDI, JALR, or immutable branch interpretation. -/
private def iTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ITypeEvent :=
  match decoded with
  | .ITYPE (imm, rs1, rd, _) => iOperands? stamped clk pc opcode rs1 rd imm
  | .JALR (imm, rs1, rd) => iOperands? stamped clk pc opcode rs1 rd imm
  | .BTYPE (imm, rs2, rs1, _) => iOperands? stamped clk pc opcode rs2 rs1 imm
  | _ => none

/-- Build the one-register J/U adapter shape. -/
private def jTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option JTypeEvent :=
  match stamped with
  | [a] =>
      match a.touch.slot with
      | .opA =>
          match decoded with
          | .UTYPE (imm, rd, _) =>
              let value := utypeImmediateNat imm
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rd).toNat
                  immB := value
                  immC := value
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous }
          | .JAL (imm, rd) =>
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rd).toNat
                  immB := (imm.signExtend 64).toNat
                  immC := 0
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous }
          | _ => none
      | _ => none
  | _ => none

/-- The common RAM/B/A adapter fields for loads and stores. -/
private def memoryOperands (ram b a : StampedTouch) (clk pc opcode : ℕ)
    (imm : BitVec 12) (rs1 opA : regidx) : MemoryEvent where
  clk := clk
  pc := pc
  opcode := opcode
  opA := (regidxBits opA).toNat
  opB := (regidxBits rs1).toNat
  imm := sextNat imm
  b := b.touch.pulled.toNat
  prevA := a.touch.pulled.toNat
  prevTsA := a.previous
  prevTsB := b.previous
  prevMem := ram.touch.pulled.toNat
  prevTsMem := ram.previous

/-- Build the RAM/B/A memory-family record. -/
private def memoryEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option MemoryEvent :=
  match stamped with
  | [ram, b, a] =>
      match ram.touch.slot, b.touch.slot, a.touch.slot with
      | .ram, .opB, .opA =>
          match decoded with
          | .LOAD (imm, rs1, rd, _, _) => some (memoryOperands ram b a clk pc opcode imm rs1 rd)
          | .STORE (imm, rs2, rs1, _) => some (memoryOperands ram b a clk pc opcode imm rs1 rs2)
          | _ => none
      | _, _, _ => none
  | _ => none

/-! ## Registry-indexed compilation -/

/-- Select the event constructor dictated by one registry identity.  This is private because its
public caller first computes the identity with `instructionRouteId`, preventing mismatched
instruction/family pairs. -/
private def instructionEventFor? (id : InstructionChipId) (decoded : instruction)
    (stamped : List StampedTouch) (clk pc opcode : ℕ) : Option id.Event :=
  match id with
  | .add => rTypeEvent? decoded stamped clk pc opcode
  | .addi => iTypeEvent? decoded stamped clk pc opcode
  | .addw => aluTypeEvent? decoded stamped clk pc opcode
  | .sub => rTypeEvent? decoded stamped clk pc opcode
  | .subw => rTypeEvent? decoded stamped clk pc opcode
  | .bitwise => aluTypeEvent? decoded stamped clk pc opcode
  | .lt => aluTypeEvent? decoded stamped clk pc opcode
  | .shiftLeft => aluTypeEvent? decoded stamped clk pc opcode
  | .shiftRight => aluTypeEvent? decoded stamped clk pc opcode
  | .jal => jTypeEvent? decoded stamped clk pc opcode
  | .jalr => iTypeEvent? decoded stamped clk pc opcode
  | .branch => iTypeEvent? decoded stamped clk pc opcode
  | .uType => jTypeEvent? decoded stamped clk pc opcode
  | .loadByte => memoryEvent? decoded stamped clk pc opcode
  | .loadHalf => memoryEvent? decoded stamped clk pc opcode
  | .loadWord => memoryEvent? decoded stamped clk pc opcode
  | .loadDouble => memoryEvent? decoded stamped clk pc opcode
  | .loadX0 => memoryEvent? decoded stamped clk pc opcode
  | .storeByte => memoryEvent? decoded stamped clk pc opcode
  | .storeHalf => memoryEvent? decoded stamped clk pc opcode
  | .storeWord => memoryEvent? decoded stamped clk pc opcode
  | .storeDouble => memoryEvent? decoded stamped clk pc opcode
  | .mul => rTypeEvent? decoded stamped clk pc opcode
  | .divRem => rTypeEvent? decoded stamped clk pc opcode
  | .aluX0 => aluTypeEvent? decoded stamped clk pc opcode

private theorem instructionEventFor?_utype {args : BitVec 20 × regidx × uop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.UTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.UTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.UTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op
  all_goals
    simp_all only [uopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, jTypeEvent?]
    rfl

private theorem instructionEventFor?_jal {args : BitVec 21 × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.JAL args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.JAL args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.JAL args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  all_goals
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, jTypeEvent?]
    rfl

private theorem instructionEventFor?_jalr {args : BitVec 12 × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.JALR args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.JALR args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.JALR args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  all_goals
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?, iOperands?]
    rfl

private theorem instructionEventFor?_btype {args : BitVec 13 × regidx × regidx × bop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.BTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.BTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.BTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs2, rs1, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op
  all_goals
    simp_all only [bopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?, iOperands?]
    rfl

private theorem instructionEventFor?_itype {args : BitVec 12 × regidx × regidx × iop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.ITYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.ITYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.ITYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [iopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?, iOperands?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_shiftiop {args : BitVec 6 × regidx × regidx × sop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.SHIFTIOP args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.SHIFTIOP args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.SHIFTIOP args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [sopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_rtype {args : regidx × regidx × regidx × rop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.RTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.RTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.RTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [ropToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_load {args : BitVec 12 × regidx × regidx × Bool × word_width}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.LOAD args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.LOAD args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.LOAD args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, isU, width⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  simp only [loadOpcode] at routed
  split_ifs at routed <;> cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, memoryEvent?]
  all_goals rfl

private theorem instructionEventFor?_store {args : BitVec 12 × regidx × regidx × word_width}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.STORE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.STORE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.STORE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs2, rs1, width⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  simp only [storeOpcode] at routed
  split_ifs at routed
  all_goals
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, memoryEvent?]
    rfl

private theorem instructionEventFor?_addiw {args : BitVec 12 × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.ADDIW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.ADDIW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.ADDIW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_rtypew {args : regidx × regidx × regidx × ropw}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.RTYPEW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.RTYPEW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.RTYPEW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [ropwToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_shiftiwop {args : BitVec 5 × regidx × regidx × sopw}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.SHIFTIWOP args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.SHIFTIWOP args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.SHIFTIWOP args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [sopwToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_mul {args : regidx × regidx × regidx × mul_op}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.MUL args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.MUL args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.MUL args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  rcases op with ⟨part, signed1, signed2⟩
  cases part <;> cases signed1 <;> cases signed2 <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [mulOpToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_mulw {args : regidx × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.MULW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.MULW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.MULW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_div {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.DIV args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.DIV args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.DIV args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_divw {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.DIVW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.DIVW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.DIVW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_rem {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.REM args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.REM args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.REM args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_remw {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.REMW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.REMW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.REMW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, instructionOperands, List.map_cons, List.map_nil, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

/-- Canonical roles make every selected family constructor total, including aliases and `x0`. -/
private theorem instructionEventFor?_isSome {id : InstructionChipId} {decoded : instruction}
    {stamped : List StampedTouch} (routed : instructionRouteId decoded = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots decoded)
    (clk pc opcode : ℕ) : (instructionEventFor? id decoded stamped clk pc opcode).isSome := by
  cases decoded <;> rename_i chunk <;> cases chunk
  case UTYPE => exact instructionEventFor?_utype routed shape clk pc opcode
  case JAL => exact instructionEventFor?_jal routed shape clk pc opcode
  case JALR => exact instructionEventFor?_jalr routed shape clk pc opcode
  case BTYPE => exact instructionEventFor?_btype routed shape clk pc opcode
  case ITYPE => exact instructionEventFor?_itype routed shape clk pc opcode
  case SHIFTIOP => exact instructionEventFor?_shiftiop routed shape clk pc opcode
  case RTYPE => exact instructionEventFor?_rtype routed shape clk pc opcode
  case LOAD => exact instructionEventFor?_load routed shape clk pc opcode
  case STORE => exact instructionEventFor?_store routed shape clk pc opcode
  case ADDIW => exact instructionEventFor?_addiw routed shape clk pc opcode
  case RTYPEW => exact instructionEventFor?_rtypew routed shape clk pc opcode
  case SHIFTIWOP => exact instructionEventFor?_shiftiwop routed shape clk pc opcode
  case MUL => exact instructionEventFor?_mul routed shape clk pc opcode
  case MULW => exact instructionEventFor?_mulw routed shape clk pc opcode
  case DIV => exact instructionEventFor?_div routed shape clk pc opcode
  case DIVW => exact instructionEventFor?_divw routed shape clk pc opcode
  case REM => exact instructionEventFor?_rem routed shape clk pc opcode
  case REMW => exact instructionEventFor?_remw routed shape clk pc opcode
  all_goals simp [instructionRouteId, instructionRouteKey] at routed

/-- The complete proof-independent result for one instruction.  The access schedule retains the
stamped instruction roles, any preceding refresh events, and the outgoing frontier in one carrier;
later compiler stages never reconstruct a parallel access model from event fields. -/
structure CompiledInstructionEvent where
  routed : RoutedEvent
  plan : InstructionAccessPlan
  schedule : AccessSchedule

namespace CompiledInstructionEvent

/-- The role-ordered timestamps copied into the instruction table's semantic event. -/
def stamped (compiled : CompiledInstructionEvent) : List StampedTouch :=
  compiled.schedule.stampedTouches

/-- Register refreshes which must precede this instruction row. -/
def memoryBumps (compiled : CompiledInstructionEvent) : List MemoryBumpEvent :=
  compiled.schedule.memoryBumps

/-- The last-access frontier after every instruction role. -/
def nextFrontier (compiled : CompiledInstructionEvent) : AccessFrontier :=
  compiled.schedule.outgoing

end CompiledInstructionEvent
/-- Compile one decoded supported transition using the canonical refresh-aware access scheduler.

At a 24-bit timestamp-window boundary `scheduleAccessPlan` inserts a register `MemoryBump` before
C/B/A and makes the instruction event cite the refreshed `base + 1` timestamp.  RAM is never
refreshed.  Thus this public compiler does not expose or accidentally substitute the older
refresh-naive `stampPlan` schedule.

Failure means exactly one of: the raw Sail constructor is outside the decoder image, the source
PC/value image is absent, routing is unsupported, or the canonical adapter shape no longer agrees
with the selected registry family. -/
def compileInstructionEvent? (view : SP1TransitionView)
    (frontier : AccessFrontier) (clk : ℕ) : Option CompiledInstructionEvent :=
  match view.accessPlan? with
  | none => none
  | some accesses =>
      let schedule := scheduleAccessPlan frontier clk accesses
      match instructionEventFor? view.chipId view.decoded schedule.stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat with
      | none => none
      | some event =>
          some
            { routed := ⟨view.chipId, event⟩
              plan := accesses
              schedule := schedule }

/-- The narrow transparent readiness boundary for one instruction event.  No row-validity theorem
or Clean witness is hidden here. -/
def InstructionEventReady (view : SP1TransitionView)
    (frontier : AccessFrontier) (clk : ℕ) : Prop :=
  (compileInstructionEvent? view frontier clk).isSome

theorem instructionEventReady_iff {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} :
    InstructionEventReady view frontier clk ↔
      ∃ result, compileInstructionEvent? view frontier clk = some result := by
  exact Option.isSome_iff_exists

/-- Canonical access extraction suffices for event compilation, for every frontier and clock.
Readiness is a derived compatibility result; it is not an extra semantic-domain condition. -/
theorem instructionEventReady_of_projection {program : GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} {plan : InstructionAccessPlan}
    (projected : projectSP1Transition? program located = some view)
    (accesses : view.accessPlan? = some plan) (frontier : AccessFrontier) (clk : ℕ) :
    InstructionEventReady view frontier clk := by
  have shape : (scheduleAccessPlan frontier clk plan).stampedTouches.map (fun touch => touch.touch.slot) =
      instructionAccessSlots view.decoded := by
    change List.map (PlannedTouch.slot ∘ StampedTouch.touch) _ = _
    rw [← List.map_map, scheduleAccessPlan_erase]
    exact instructionAccessPlan_slots ((projectSP1Transition?_accesses projected).trans accesses)
  obtain ⟨event, generated⟩ := Option.isSome_iff_exists.mp
    (instructionEventFor?_isSome (projectSP1Transition?_route projected) shape clk
      view.pc.toNat view.routeKey.opcode.toNat)
  simp only [InstructionEventReady, compileInstructionEvent?, accesses, generated, Option.isSome_some]

/-- Successful compilation exposes each proof-independent projection used by the `do` block. -/
private theorem compileInstructionEvent?_components {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    ∃ accesses event,
      view.accessPlan? = some accesses ∧
      instructionEventFor? view.chipId view.decoded
          (scheduleAccessPlan frontier clk accesses).stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat = some event ∧
        result =
          { routed := ⟨view.chipId, event⟩
            plan := accesses
            schedule := scheduleAccessPlan frontier clk accesses } := by
  unfold compileInstructionEvent? at generated
  cases accessEq : view.accessPlan? with
  | none => simp [accessEq] at generated
  | some accesses =>
      simp only [accessEq] at generated
      cases eventEq : instructionEventFor? view.chipId view.decoded
          (scheduleAccessPlan frontier clk accesses).stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat with
      | none => simp [eventEq] at generated
      | some event =>
          rw [eventEq] at generated
          simp only [Option.some.injEq] at generated
          exact ⟨accesses, event, rfl, eventEq, generated.symm⟩

private theorem rTypeEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : RTypeEvent}
    (built : rTypeEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold rTypeEvent? at built
  obtain ⟨_, _, built⟩ := Option.bind_eq_some_iff.mp built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem aluRegisterEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : ALUTypeEvent}
    (built : aluRegisterEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold aluRegisterEvent? at built
  obtain ⟨_, _, built⟩ := Option.bind_eq_some_iff.mp built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem aluImmediateEventOf?_coordinates (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec 64) {event : ALUTypeEvent}
    (built : aluImmediateEventOf? stamped clk pc opcode rs1 rd immediate = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold aluImmediateEventOf? at built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem aluTypeEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : ALUTypeEvent}
    (built : aluTypeEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold aluTypeEvent? at built
  repeat' split at built
  all_goals first | exact aluImmediateEventOf?_coordinates _ _ _ _ _ _ _ built | exact aluRegisterEvent?_coordinates _ _ _ _ _ built

private theorem iOperands?_coordinates {width : ℕ} (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec width) {event : ITypeEvent}
    (built : iOperands? stamped clk pc opcode rs1 rd immediate = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold iOperands? at built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem iTypeEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : ITypeEvent}
    (built : iTypeEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold iTypeEvent? at built
  repeat' split at built
  all_goals first | exact iOperands?_coordinates _ _ _ _ _ _ _ built | cases built

private theorem jTypeEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : JTypeEvent}
    (built : jTypeEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold jTypeEvent? at built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem memoryEvent?_coordinates (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) {event : MemoryEvent}
    (built : memoryEvent? decoded stamped clk pc opcode = some event) : event.clk = clk ∧ event.pc = pc := by
  unfold memoryEvent? at built
  repeat' split at built
  all_goals cases built
  all_goals exact ⟨rfl, rfl⟩

private theorem instructionEventFor?_coordinates {id : InstructionChipId} {event : id.Event}
    {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ}
    (built : instructionEventFor? id decoded stamped clk pc opcode = some event) :
    (RoutedEvent.mk id event).clock = clk ∧ (RoutedEvent.mk id event).pc = pc := by
  cases id <;> first
    | exact rTypeEvent?_coordinates _ _ _ _ _ built
    | exact aluTypeEvent?_coordinates _ _ _ _ _ built
    | exact iTypeEvent?_coordinates _ _ _ _ _ built
    | exact jTypeEvent?_coordinates _ _ _ _ _ built
    | exact memoryEvent?_coordinates _ _ _ _ _ built

/-- The registry-indexed event retains the exact timestamp and PC of its input transition. -/
theorem compileInstructionEvent?_coordinates {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    result.routed.clock = clk ∧ result.routed.pc = view.pc.toNat := by
  obtain ⟨_, _, _, built, rfl⟩ := compileInstructionEvent?_components generated
  exact instructionEventFor?_coordinates built

/-- Compilation cannot invent or relabel a route: the dependent event carries exactly the identity
selected by the canonical semantic router. -/
theorem compileInstructionEvent?_route {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    result.routed.id = view.chipId := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  rfl

/-- The result retains the exact canonical access plan returned by the field-free extractor. -/
theorem compileInstructionEvent?_accessPlan {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    view.accessPlan? = some result.plan := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact accessEq

/-- For a retained shared transition projection, the compiler plan is literally the canonical
Model-layer plan of that source/target pair. -/
theorem compileInstructionEvent?_accessPlan_generated
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result) :
    instructionAccessPlan? view.decoded located.source located.transition.target =
      some result.plan := by
  rw [projectSP1Transition?_accesses projected]
  exact compileInstructionEvent?_accessPlan generated

/-- The routed event retains exactly the schedule applied to its original incoming frontier,
including all high-window refreshes and the order of aliased operands. -/
theorem compileInstructionEvent?_schedule {view : SP1TransitionView} {frontier : AccessFrontier}
    {clk : ℕ} {result : CompiledInstructionEvent} (generated : compileInstructionEvent? view frontier clk = some result) :
    result.schedule = scheduleAccessPlan frontier clk result.plan := by
  obtain ⟨_, _, _, _, rfl⟩ := compileInstructionEvent?_components generated
  rfl

/-- The outgoing compiler clock is the last real touch at each location, also across refreshes. -/
theorem compileInstructionEvent?_nextFrontier {view : SP1TransitionView} {frontier : AccessFrontier}
    {clk : ℕ} {result : CompiledInstructionEvent} (generated : compileInstructionEvent? view frontier clk = some result) :
    result.nextFrontier = advancePlan frontier clk result.plan := by
  obtain ⟨accesses, event, _, _, rfl⟩ := compileInstructionEvent?_components generated
  exact scheduleAccessPlan_outgoing frontier clk accesses

/-- Stamping is not a second access representation: erasing its timestamps returns the retained
canonical plan literally. -/
theorem compileInstructionEvent?_stamped_touches {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    result.stamped.map StampedTouch.touch = result.plan := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_erase frontier clk accesses

/-- A well-formed extracted plan and a bounded incoming frontier make every timestamp copied into
the event strictly earlier than its own current access.  This discharges the timestamp half of all
four adapter-family `WellFormed` predicates without any instruction-specific semantic premise. -/
theorem compileInstructionEvent?_timestamps {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (wellFormed : result.plan.WellFormed)
    (bounded : frontier.BoundedAt clk) :
    ∀ stamped ∈ result.stamped, stamped.previous < stamped.current clk := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_previous_lt wellFormed bounded

/-- Every refresh inserted for a compiled row satisfies the MemoryBump event boundary. -/
theorem compileInstructionEvent?_memoryBumps_wellFormed {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (wellFormed : result.plan.WellFormed)
    (bounded : frontier.BoundedAt clk) (aligned : clk % ordinaryClkInc = 1)
    (currLt : clk + 1 < 2 ^ 48) :
    ∀ event ∈ result.memoryBumps, event.WellFormed := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_memoryBumps_wellFormed
    wellFormed bounded aligned currLt

/-- The scheduler returns a frontier valid at the following ordinary row. -/
theorem compileInstructionEvent?_frontier_bounded_next {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : frontier.BoundedAt clk) :
    result.nextFrontier.BoundedAt (clk + ordinaryClkInc) := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_outgoing_bounded_next accesses bounded


private theorem regidx_decide_x0 (rd : regidx) :
    decide ((regidxBits rd).toNat = 0) = regidxIsX0 rd := by
  cases rd with
  | Regidx idx =>
    by_cases zero : idx = 0
    · simp [regidxBits, regidxIsX0, zero]
    · have nz : idx.toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
      simpa [regidxBits, regidxIsX0, nz] using zero

private theorem cbaRegisters?_destination {decoded : instruction}
    {registers : BitVec 5 × BitVec 5 × BitVec 5} {key : InstructionRouteKey}
    (extracted : cbaRegisters? decoded = some registers) (keyEq : instructionRouteKey decoded = some key) :
    decide (registers.2.2.toNat = 0) = key.opAIsX0 := by
  cases decoded <;> rename_i chunk <;> cases chunk <;> simp only [cbaRegisters?] at extracted
  all_goals try contradiction
  all_goals
    cases Option.some.inj extracted
    cases Option.some.inj keyEq
    exact regidx_decide_x0 _

/-- Both ALU destinations share operand and timestamp bounds. The routed zero destination
uses the architectural zero read, while the ordinary destination carries a displaced word. -/
private def ALUDestinationValid (event : ALUTypeEvent) (key : InstructionRouteKey) : Prop :=
  event.opcode = key.opcode.toNat ∧
  (key.opAIsX0 = false → event.WellFormed) ∧
  (key.opAIsX0 = true → event.opcode < 29 → event.WellFormedX0)

private theorem aluDestinationValid_of_fields {e : ALUTypeEvent} {key : InstructionRouteKey}
    (opcode : e.opcode = key.opcode.toNat) (phase : e.clk % 8 = 1) (pc : e.pc < 2 ^ 48)
    (a : e.opA < 32) (b : e.opB < 32) (dst : decide (e.opA = 0) = key.opAIsX0)
    (imm : e.immC = 0 ∨ e.immC = 1) (c : e.opC < 2 ^ 64) (reg : e.immC = 0 → e.opC < 32)
    (bVal : e.b < 2 ^ 64) (cVal : e.c < 2 ^ 64) (prior : e.prevA < 2 ^ 64)
    (x0 : key.opAIsX0 = true → e.prevA = 0) (aTime : e.prevTsA < e.clk + 4)
    (bTime : e.prevTsB < e.clk + 3) (cTime : e.immC = 0 → e.prevTsC < e.clk + 2) :
    ALUDestinationValid e key :=
  ⟨opcode, fun nz => ⟨phase, pc, a, b, decide_eq_false_iff_not.mp (dst.trans nz), imm, c, reg,
    bVal, cVal, prior, aTime, bTime, cTime⟩,
   fun z op => ⟨phase, pc, of_decide_eq_true (dst.trans z), b, op, imm, c, reg,
    bVal, cVal, x0 z, aTime, bTime, cTime⟩⟩

private theorem aluRegisterEvent?_wellFormed {decoded : instruction}
    {stamped : List StampedTouch} {clk pc : ℕ} {key : InstructionRouteKey} {event : ALUTypeEvent}
    (keyEq : instructionRouteKey decoded = some key)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : aluRegisterEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    ALUDestinationValid event key := by
  unfold aluRegisterEvent? at generated
  cases registersEq : cbaRegisters? decoded with
  | none => simp [registersEq] at generated
  | some registers =>
    simp only [registersEq] at generated
    split at generated
    · rename_i original c b a
      split at generated
      · rename_i cSlot bSlot aSlot
        cases Option.some.inj generated
        have cTime := ordered c (by simp)
        have bTime := ordered b (by simp)
        have aTime := ordered a (by simp)
        simp only [StampedTouch.current, PlannedTouch.recordTime, cSlot, bSlot, aSlot,
          AccessSlot.recordOffset_opC, AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at cTime bTime aTime
        exact aluDestinationValid_of_fields rfl phase pcBound registers.2.2.isLt registers.2.1.isLt
          (cbaRegisters?_destination registersEq keyEq) (Or.inl rfl)
          (lt_trans registers.1.isLt (by decide)) (fun _ => registers.1.isLt)
          b.touch.pulled.isLt c.touch.pulled.isLt a.touch.pulled.isLt
          (fun z => congrArg BitVec.toNat (prior z a (by simp) aSlot)) aTime bTime (fun _ => cTime)
      · contradiction
    · contradiction

private theorem aluImmediateEventOf?_wellFormed {stamped : List StampedTouch} {clk pc : ℕ}
    {key : InstructionRouteKey} {rs1 rd : regidx} {imm : BitVec 64} {event : ALUTypeEvent}
    (rdKey : regidxIsX0 rd = key.opAIsX0)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : aluImmediateEventOf? stamped clk pc key.opcode.toNat rs1 rd imm = some event) :
    ALUDestinationValid event key := by
  unfold aluImmediateEventOf? at generated
  split at generated
  · rename_i original b a
    split at generated
    · rename_i bSlot aSlot
      cases Option.some.inj generated
      have bTime := ordered b (by simp)
      have aTime := ordered a (by simp)
      simp only [StampedTouch.current, PlannedTouch.recordTime, bSlot, aSlot,
        AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at bTime aTime
      have dst := (regidx_decide_x0 rd).trans rdKey
      exact aluDestinationValid_of_fields rfl phase pcBound (regidxBits rd).isLt (regidxBits rs1).isLt
        dst (Or.inr rfl) imm.isLt (by simp) b.touch.pulled.isLt (Nat.two_pow_pos _) a.touch.pulled.isLt
        (fun z => congrArg BitVec.toNat (prior z a (by simp) aSlot)) aTime bTime (by simp)
    · contradiction
  · contradiction

private theorem aluTypeEvent?_wellFormed {decoded : instruction}
    {stamped : List StampedTouch} {clk pc : ℕ} {key : InstructionRouteKey} {event : ALUTypeEvent}
    (keyEq : instructionRouteKey decoded = some key)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : aluTypeEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    ALUDestinationValid event key := by
  unfold aluTypeEvent? at generated
  split at generated
  all_goals first
    | exact aluRegisterEvent?_wellFormed keyEq prior phase pcBound ordered generated
    | cases Option.some.inj keyEq
      exact aluImmediateEventOf?_wellFormed rfl prior phase pcBound ordered generated

private theorem iOperands?_jalr_fields {stamped : List StampedTouch} {clk pc opcode width : ℕ}
    {rs1 rd : regidx} {imm : BitVec width} {event : ITypeEvent}
    (prior : regidxIsX0 rd = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : iOperands? stamped clk pc opcode rs1 rd imm = some event) :
    event.WellFormedJalr ∧ event.opcode = opcode ∧ decide (event.opA = 0) = regidxIsX0 rd := by
  unfold iOperands? at generated
  split at generated
  · rename_i original b a
    split at generated
    · rename_i bSlot aSlot
      cases Option.some.inj generated
      have bTime := ordered b (by simp)
      have aTime := ordered a (by simp)
      simp only [StampedTouch.current, PlannedTouch.recordTime, bSlot, aSlot,
        AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at bTime aTime
      refine ⟨⟨phase, pcBound, (regidxBits rd).isLt, (regidxBits rs1).isLt,
        (imm.signExtend 64).isLt, b.touch.pulled.isLt, a.touch.pulled.isLt, ?_, aTime, bTime⟩, rfl, regidx_decide_x0 rd⟩
      intro zero
      have z := (regidx_decide_x0 rd).symm.trans (decide_eq_true zero)
      exact congrArg BitVec.toNat (prior z a (by simp) aSlot)
    · contradiction
  · contradiction

private theorem iTypeEvent?_adapter_fields {decoded : instruction} {stamped : List StampedTouch}
    {clk pc : ℕ} {key : InstructionRouteKey} {event : ITypeEvent}
    (keyEq : instructionRouteKey decoded = some key)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : iTypeEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    event.WellFormedJalr ∧ event.opcode = key.opcode.toNat ∧ decide (event.opA = 0) = key.opAIsX0 := by
  unfold iTypeEvent? at generated
  split at generated
  all_goals first
    | contradiction
    | cases Option.some.inj keyEq
      exact iOperands?_jalr_fields prior phase pcBound ordered generated

private theorem rTypeEvent?_wellFormed {decoded : instruction}
    {stamped : List StampedTouch} {clk pc : ℕ} {key : InstructionRouteKey} {event : RTypeEvent}
    (keyEq : instructionRouteKey decoded = some key) (nonzero : key.opAIsX0 = false)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : rTypeEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    event.WellFormed ∧ event.opcode = key.opcode.toNat := by
  unfold rTypeEvent? at generated
  cases registersEq : cbaRegisters? decoded with
  | none => simp [registersEq] at generated
  | some registers =>
    simp only [registersEq] at generated
    split at generated
    · rename_i original c b a
      split at generated
      · rename_i cSlot bSlot aSlot
        cases Option.some.inj generated
        have cTime := ordered c (by simp)
        have bTime := ordered b (by simp)
        have aTime := ordered a (by simp)
        simp only [StampedTouch.current, PlannedTouch.recordTime, cSlot, bSlot, aSlot,
          AccessSlot.recordOffset_opC, AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at cTime bTime aTime
        exact ⟨⟨phase, pcBound, registers.2.2.isLt, registers.2.1.isLt, registers.1.isLt,
          decide_eq_false_iff_not.mp ((cbaRegisters?_destination registersEq keyEq).trans nonzero),
          b.touch.pulled.isLt, c.touch.pulled.isLt, a.touch.pulled.isLt,
          aTime, bTime, cTime⟩, rfl⟩
      · contradiction
    · contradiction
private theorem projected_instruction_fields {program : GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} (projected : projectSP1Transition? program located = some view) :
    view.pc.toNat < 2 ^ 48 ∧ instructionRouteKey view.decoded = some view.routeKey ∧
      view.chipId.route.claims view.routeKey.opcode view.routeKey.opAIsX0 = true := by
  have components := projectSP1Transition?_components projected
  have pcBound : view.pc.toNat < 2 ^ 48 := by
    obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp components.2.1
    have same : entry.1 = view.pc := by simpa only [beq_iff_eq] using List.find?_some found
    have window := program.rom_in_window entry (List.mem_of_find?_eq_some found)
    rw [same] at window
    omega
  have keyEq := components.2.2.2.2.1
  have routed := components.2.2.2.2.2.1
  have claimed : view.chipId.route.claims view.routeKey.opcode view.routeKey.opAIsX0 = true := by
    rw [instructionRouteId, keyEq, Option.bind_some] at routed
    change (fun id => id.route.claims view.routeKey.opcode view.routeKey.opAIsX0) view.chipId = true
    exact List.find?_some (p := fun id : InstructionChipId =>
      id.route.claims view.routeKey.opcode view.routeKey.opAIsX0) routed
  exact ⟨pcBound, keyEq, claimed⟩

/-- The five R-type adapter tables obtain their complete event validity from canonical projection
and the running scheduler invariant. Operand bounds come from the bitvectors themselves; routing
supplies the destination and opcode conditions. This includes all multiply/divide/remainder values,
without any nonzero-divisor or no-overflow restriction. -/
theorem compileInstructionEvent?_rtype_valid
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (family : view.chipId ∈ [.add, .sub, .subw, .mul, .divRem])
    (phase : clk % 8 = 1) (bounded : frontier.BoundedAt clk) :
    result.routed.id.Valid result.routed.event := by
  obtain ⟨pcBound, keyEq, claimed⟩ := projected_instruction_fields projected
  have wellFormed := instructionAccessPlan_wellFormed
    (compileInstructionEvent?_accessPlan_generated projected generated)
  have ordered := compileInstructionEvent?_timestamps generated wellFormed bounded
  rcases view with ⟨pc, word, decoded, key, id, plan⟩
  dsimp only at family claimed keyEq pcBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at family
  rcases family with rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
    have nonzero : key.opAIsX0 = false := by
      simpa only [InstructionChipId.route, RdGuard.holds, Bool.not_eq_true']
        using (Bool.and_eq_true_iff.mp claimed).2
    have valid := rTypeEvent?_wellFormed keyEq nonzero phase pcBound ordered constructed
  · exact valid.1
  · exact valid.1
  · exact valid.1
  · refine ⟨valid.1, ?_⟩
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds,
      Bool.and_eq_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    rcases claimed.1 with h | h | h | h | h <;>
      simp [RTypeEvent.IsMul, valid.2, h, Soundness.Opcode.toNat]
  · refine ⟨valid.1, ?_⟩
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds,
      Bool.and_eq_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    rcases claimed.1 with h | h | h | h | h | h | h | h <;>
      simp [RTypeEvent.IsDivRem, valid.2, h, Soundness.Opcode.toNat]

private theorem compiled_x0_pulled {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (zero : view.routeKey.opAIsX0 = true) (t : StampedTouch) (member : t ∈ result.stamped)
    (slot : t.touch.slot = .opA) : t.touch.pulled = 0 := by
  apply instructionAccessPlan_opA_x0 (compileInstructionEvent?_accessPlan_generated projected generated)
    (projected_instruction_fields projected).2.1 zero _ slot
  rw [← compileInstructionEvent?_stamped_touches generated]
  exact List.mem_map_of_mem member

private theorem aluX0_opcode_lt {opcode : Soundness.Opcode}
    (claimed : InstructionChipId.aluX0.route.claims opcode true = true) : opcode.toNat < 29 := by
  cases opcode <;> first | decide | contradiction

/-- Validity of the immediate-add, word-add, bitwise, comparison, shift, and zero-destination ALU
rows. The opcode and destination follow from the released instruction routing key, and every
register timestamp is taken from the scheduled accesses. -/
theorem compileInstructionEvent?_alu_valid
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (family : view.chipId ∈ [.aluX0, .addi, .addw, .bitwise, .lt, .shiftLeft, .shiftRight])
    (phase : clk % 8 = 1) (bounded : frontier.BoundedAt clk) :
    result.routed.id.Valid result.routed.event := by
  obtain ⟨pcBound, keyEq, claimed⟩ := projected_instruction_fields projected
  have ordered := compileInstructionEvent?_timestamps generated
    (instructionAccessPlan_wellFormed (compileInstructionEvent?_accessPlan_generated projected generated)) bounded
  have prior := compiled_x0_pulled projected generated
  rcases view with ⟨pc, word, decoded, key, id, plan⟩
  dsimp only at family claimed keyEq pcBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at family
  rcases family with rfl | nonzero
  · obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
    have zero : key.opAIsX0 = true := (Bool.and_eq_true_iff.mp claimed).2
    have valid := aluTypeEvent?_wellFormed keyEq prior phase pcBound ordered constructed
    apply valid.2.2 zero
    rw [valid.1]
    rw [zero] at claimed
    exact aluX0_opcode_lt claimed
  rcases nonzero with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds, Bool.and_eq_true,
      Bool.not_eq_true', List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
  · obtain ⟨wf, _, dest⟩ := iTypeEvent?_adapter_fields keyEq prior phase pcBound ordered constructed
    exact ⟨wf.clk_mod, wf.pc_lt, wf.opA_lt, wf.opB_lt, decide_eq_false_iff_not.mp (dest.trans claimed.2),
      wf.imm_lt, wf.b_lt, wf.prevA_lt, wf.prevTsA_lt, wf.prevTsB_lt⟩
  all_goals have valid := aluTypeEvent?_wellFormed keyEq prior phase pcBound ordered constructed
  · exact valid.2.1 claimed.2
  all_goals refine ⟨valid.2.1 claimed.2, ?_⟩
  · rcases claimed.1 with h | h | h <;> simp [ALUTypeEvent.IsBitwise, valid.1, h, Soundness.Opcode.toNat]
  · rcases claimed.1 with h | h <;> simp [ALUTypeEvent.IsLt, valid.1, h, Soundness.Opcode.toNat]
  · rcases claimed.1 with h | h <;> simp [ALUTypeEvent.IsShiftLeft, valid.1, h, Soundness.Opcode.toNat]
  · rcases claimed.1 with h | h | h | h <;> simp [ALUTypeEvent.IsShiftRight, valid.1, h, Soundness.Opcode.toNat]

private theorem jTypeEvent?_adapter_fields {decoded : instruction} {stamped : List StampedTouch}
    {clk pc : ℕ} {key : InstructionRouteKey} {event : JTypeEvent}
    (keyEq : instructionRouteKey decoded = some key)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : jTypeEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    event.WellFormedJal ∧ event.opcode = key.opcode.toNat ∧
      (event.IsUType → event.UTypeImm) := by
  unfold jTypeEvent? at generated
  split at generated
  · rename_i original a
    split at generated
    · rename_i aSlot
      have aTime := ordered a (by simp)
      simp only [StampedTouch.current, PlannedTouch.recordTime, aSlot, AccessSlot.recordOffset_opA] at aTime
      split at generated
      · rename_i imm rd op
        cases Option.some.inj keyEq
        cases Option.some.inj generated
        have immBound := ((imm.signExtend 64) <<< 12).isLt
        refine ⟨⟨phase, pcBound, (regidxBits rd).isLt, immBound, immBound, a.touch.pulled.isLt,
          ?_, aTime⟩, rfl, fun _ => ⟨imm.toNat, imm.isLt, utypeImmediateNat_eq_luiImmNat imm⟩⟩
        intro zero
        exact congrArg BitVec.toNat (prior ((regidx_decide_x0 rd).symm.trans (decide_eq_true zero)) a (by simp) aSlot)
      · rename_i imm rd
        cases Option.some.inj keyEq
        cases Option.some.inj generated
        refine ⟨⟨phase, pcBound, (regidxBits rd).isLt, (imm.signExtend 64).isLt,
          Nat.two_pow_pos _, a.touch.pulled.isLt, ?_, aTime⟩, rfl, fun h => ?_⟩
        · intro zero
          exact congrArg BitVec.toNat (prior ((regidx_decide_x0 rd).symm.trans (decide_eq_true zero)) a (by simp) aSlot)
        · change Soundness.Opcode.JAL.toNat = 48 ∨ Soundness.Opcode.JAL.toNat = 49 at h
          simp [Soundness.Opcode.toNat] at h
      · contradiction
    · contradiction
  · contradiction

/-- Target conditions selected by the three released control-flow adapters. The remaining
instruction tables do not use a control-flow successor as a witness input. -/
def RoutedEvent.ControlTargets : RoutedEvent → Prop
  | ⟨.jal, e⟩ => e.JalTargets
  | ⟨.jalr, e⟩ => e.JalrTargets
  | ⟨.branch, e⟩ => e.BranchTargets
  | _ => True

/-- The canonical J/U and two-source I adapters supply every operand, x0 read-back, opcode
selector and predecessor timestamp. The decoders also supply the sign-extended U immediate.
Only the selected control destination and enabled link remain for execution to determine. -/
theorem compileInstructionEvent?_control_valid_of_targets
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (family : view.chipId ∈ [.jal, .jalr, .branch, .uType])
    (phase : clk % 8 = 1) (bounded : frontier.BoundedAt clk) (target : result.routed.ControlTargets) :
    result.routed.id.Valid result.routed.event := by
  obtain ⟨pcBound, keyEq, claimed⟩ := projected_instruction_fields projected
  have ordered := compileInstructionEvent?_timestamps generated
    (instructionAccessPlan_wellFormed (compileInstructionEvent?_accessPlan_generated projected generated)) bounded
  have prior := compiled_x0_pulled projected generated
  rcases view with ⟨pc, word, decoded, key, id, plan⟩
  dsimp only at family claimed keyEq pcBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at family
  rcases family with rfl | rfl | rfl | rfl
  all_goals obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  · exact ⟨(jTypeEvent?_adapter_fields keyEq prior phase pcBound ordered constructed).1, target⟩
  · exact ⟨(iTypeEvent?_adapter_fields keyEq prior phase pcBound ordered constructed).1, target⟩
  · obtain ⟨wf, opcode, _⟩ := iTypeEvent?_adapter_fields keyEq prior phase pcBound ordered constructed
    refine ⟨⟨wf.clk_mod, wf.pc_lt, wf.opA_lt, wf.opB_lt, wf.imm_lt, wf.prevA_lt,
      wf.b_lt, wf.prevA_eq_zero, wf.prevTsA_lt, wf.prevTsB_lt⟩, ?_, target⟩
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds, Bool.and_true,
      List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    rcases claimed with h | h | h | h | h | h <;> simp [ITypeEvent.IsBranch, opcode, h, Soundness.Opcode.toNat]
  · obtain ⟨wf, opcode, imm⟩ := jTypeEvent?_adapter_fields keyEq prior phase pcBound ordered constructed
    have supported : event.IsUType := by
      simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds, Bool.and_true,
        List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
      rcases claimed with h | h <;> simp [JTypeEvent.IsUType, opcode, h, Soundness.Opcode.toNat]
    exact ⟨⟨wf.clk_mod, wf.pc_lt, wf.opA_lt, supported, wf.immB_lt, wf.immC_lt,
      wf.prevA_lt, wf.prevA_eq_zero, wf.prevTsA_lt⟩, imm supported⟩

/-- Byte accesses impose no additional address alignment. The remaining variants require the
decoded width. Only opcodes from the native load/store image use this projection. -/
private def memoryAlignment : Soundness.Opcode → ℕ
  | .LH | .LHU | .SH => 2
  | .LW | .LWU | .SW => 4
  | .LD | .SD => 8
  | _ => 1

private theorem load_alignment {w : word_width} {u : Bool} (image : loadWidthOK w u = true) :
    0 < w.toNat ∧ memoryAlignment (loadOpcode w u) = w.toNat := by
  simp only [loadWidthOK, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at image
  rcases image with ((rfl | rfl) | rfl) | ⟨rfl, _⟩ <;> cases u <;> decide

private theorem store_alignment {w : word_width} (image : storeWidthOK w = true) :
    0 < w.toNat ∧ memoryAlignment (storeOpcode w) = w.toNat := by
  simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at image
  rcases image with ((rfl | rfl) | rfl) | rfl <;> decide

private theorem memoryOperands_fields {key : InstructionRouteKey} {clk pc : ℕ}
    {ram b a : StampedTouch} {rs1 dst : regidx} {imm : BitVec 12} {width : ℕ}
    (rd : regidxIsX0 dst = key.opAIsX0)
    (prior : key.opAIsX0 = true → a.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48) (clkBound : clk < 2 ^ 48)
    (positive : 0 < width) (widthEq : memoryAlignment key.opcode = width)
    (span : NativeLayout.guestMemory.ContainsSpan (memoryEffectiveAddress b.touch.pulled imm).toNat width)
    (aligned : (memoryEffectiveAddress b.touch.pulled imm).toNat % width = 0)
    (ramTime : ram.previous < clk + 1) (bTime : b.previous < clk + 3) (aTime : a.previous < clk + 4) :
    let e := memoryOperands ram b a clk pc key.opcode.toNat imm rs1 dst
    e.WellFormedStore ∧ decide (e.opA = 0) = key.opAIsX0 ∧ e.opcode = key.opcode.toNat ∧
      e.Aligned (memoryAlignment key.opcode) := by
  let e := memoryOperands ram b a clk pc key.opcode.toNat imm rs1 dst
  have addr : e.addr = (memoryEffectiveAddress b.touch.pulled imm).toNat := by
    simp only [e, memoryOperands, MemoryEvent.addr, memoryEffectiveAddress, sextNat, BitVec.toNat_add]
  have addressBound : (memoryEffectiveAddress b.touch.pulled imm).toNat < 2 ^ 48 := by
    have high : (memoryEffectiveAddress b.touch.pulled imm).toNat + width ≤ 2 ^ 48 := span.2
    omega
  have zero := (regidx_decide_x0 dst).trans rd
  refine ⟨⟨phase, pcBound, (regidxBits dst).isLt, (regidxBits rs1).isLt,
    (imm.signExtend 64).isLt, b.touch.pulled.isLt, a.touch.pulled.isLt, ?_,
    aTime, bTime, clkBound, addr ▸ addressBound, addr ▸ span.1, ram.touch.pulled.isLt, ramTime⟩,
    zero, rfl, ?_⟩
  · intro z
    exact congrArg BitVec.toNat (prior (zero.symm.trans (decide_eq_true z)))
  · change e.addr % memoryAlignment key.opcode = 0
    rwa [addr, widthEq]

private theorem memoryEvent?_fields {decoded : instruction} {stamped : List StampedTouch}
    {source : SailState} {clk pc : ℕ} {key : InstructionRouteKey} {event : MemoryEvent}
    (keyEq : instructionRouteKey decoded = some key) (image : instructionImageOK decoded = true)
    (encoded : instructionMemoryEncoded source.get_reg? decoded)
    (baseRead : ∀ t ∈ stamped, t.touch.slot = .opB →
      match (generalizing := false) decoded with
      | .LOAD (_, rs1, _, _, _) | .STORE (_, _, rs1, _) => source.get_reg? (regidxBits rs1) = some t.touch.pulled
      | _ => True)
    (prior : key.opAIsX0 = true → ∀ t ∈ stamped, t.touch.slot = .opA → t.touch.pulled = 0)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48) (clkBound : clk < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : memoryEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    event.WellFormedStore ∧ decide (event.opA = 0) = key.opAIsX0 ∧
      event.opcode = key.opcode.toNat ∧ event.Aligned (memoryAlignment key.opcode) := by
  unfold memoryEvent? at generated
  split at generated
  · rename_i original ram b a
    split at generated
    · rename_i ramSlot bSlot aSlot
      have aTime := ordered a (by simp)
      have bTime := ordered b (by simp)
      have ramTime := ordered ram (by simp)
      simp only [StampedTouch.current, PlannedTouch.recordTime, ramSlot, bSlot, aSlot,
        AccessSlot.recordOffset_ram, AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at ramTime bTime aTime
      have read := baseRead b (by simp) bSlot
      split at generated
      next imm rs1 dst u width =>
        obtain ⟨positive, size⟩ := load_alignment (w := width) (u := u) image
        cases Option.some.inj keyEq
        cases Option.some.inj generated
        obtain ⟨base, actual, span, aligned⟩ := encoded
        cases Option.some.inj (actual.symm.trans read)
        exact memoryOperands_fields rfl (fun z => prior z a (by simp) aSlot) phase pcBound clkBound
          positive size span aligned ramTime bTime aTime
      next imm rs2 rs1 width =>
        obtain ⟨positive, size⟩ := store_alignment (w := width) image
        cases Option.some.inj keyEq
        cases Option.some.inj generated
        obtain ⟨base, actual, span, aligned⟩ := encoded
        cases Option.some.inj (actual.symm.trans read)
        exact memoryOperands_fields rfl (fun z => prior z a (by simp) aSlot) phase pcBound clkBound
          positive size span aligned ramTime bTime aTime
      next => contradiction
    · contradiction
  · contradiction

private theorem load_wellFormed {e : MemoryEvent} (wf : e.WellFormedStore) (nonzero : e.opA ≠ 0) :
    e.WellFormed :=
  ⟨⟨wf.clk_mod, wf.pc_lt, wf.opA_lt, wf.opB_lt, nonzero, wf.imm_lt, wf.b_lt,
    wf.prevA_lt, wf.prevTsA_lt, wf.prevTsB_lt⟩, wf.clk_lt, wf.addr_lt, wf.addr_ge, wf.prevMem_lt, wf.prevTsMem_lt⟩

private theorem loadX0_wellFormed {e : MemoryEvent} (wf : e.WellFormedStore) (zero : e.opA = 0) :
    e.WellFormedX0 :=
  ⟨wf.clk_mod, wf.pc_lt, zero, wf.opB_lt, wf.imm_lt, wf.b_lt, wf.prevA_x0 zero,
    wf.prevTsA_lt, wf.prevTsB_lt, wf.clk_lt, wf.addr_lt, wf.addr_ge, wf.prevMem_lt, wf.prevTsMem_lt⟩

/-- All nine memory adapters obtain their side conditions from the existing execution encoding
at the actual base register and the canonical RAM/B/A schedule. Loads to x0 and stores from x0
preserve their respective routed zero-register behavior. -/
theorem compileInstructionEvent?_memory_valid
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (family : view.chipId ∈ [.loadByte, .loadHalf, .loadWord, .loadDouble, .loadX0,
      .storeByte, .storeHalf, .storeWord, .storeDouble])
    (encoded : instructionMemoryEncoded located.source.get_reg? view.decoded)
    (phase : clk % 8 = 1) (clkBound : clk < 2 ^ 48) (bounded : frontier.BoundedAt clk) :
    result.routed.id.Valid result.routed.event := by
  obtain ⟨pcBound, keyEq, claimed⟩ := projected_instruction_fields projected
  have plan := compileInstructionEvent?_accessPlan_generated projected generated
  have ordered := compileInstructionEvent?_timestamps generated (instructionAccessPlan_wellFormed plan) bounded
  have prior := compiled_x0_pulled projected generated
  have image := (projectSP1Transition?_components projected).2.2.2.1
  have baseRead := fun (t : StampedTouch) (member : t ∈ result.stamped) (slot : t.touch.slot = .opB) =>
    instructionAccessPlan_memory_base plan
      (show t.touch ∈ result.plan by rw [← compileInstructionEvent?_stamped_touches generated]; exact List.mem_map_of_mem member) slot
  rcases view with ⟨pc, word, decoded, key, id, accessPlan⟩
  dsimp only at family claimed keyEq pcBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at family
  rcases family with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
    obtain ⟨wf, dest, opcode, aligned⟩ := memoryEvent?_fields keyEq image encoded baseRead prior
      phase pcBound clkBound ordered constructed
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds, Bool.and_eq_true,
      Bool.not_eq_true', Bool.and_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
  · refine ⟨load_wellFormed wf (decide_eq_false_iff_not.mp (dest.trans claimed.2)), ?_⟩
    rcases claimed.1 with h | h <;> simp [opcode, h, Soundness.Opcode.toNat]
  · refine ⟨load_wellFormed wf (decide_eq_false_iff_not.mp (dest.trans claimed.2)), ?_⟩
    rcases claimed.1 with h | h <;> simpa only [h, memoryAlignment] using aligned
  · refine ⟨load_wellFormed wf (decide_eq_false_iff_not.mp (dest.trans claimed.2)), ?_⟩
    rcases claimed.1 with h | h <;> simpa only [h, memoryAlignment] using aligned
  · exact ⟨load_wellFormed wf (decide_eq_false_iff_not.mp (dest.trans claimed.2)),
      by simpa only [claimed.1, memoryAlignment] using aligned⟩
  · refine ⟨loadX0_wellFormed wf (of_decide_eq_true (dest.trans claimed.2)), ?_⟩
    rcases claimed.1 with h | h | h | h | h | h | h <;>
      simp [MemoryEvent.IsLoad, opcode, h, Soundness.Opcode.toNat] <;>
      simpa only [h, memoryAlignment, MemoryEvent.Aligned] using aligned
  · exact wf
  · exact ⟨wf, by simpa only [claimed, memoryAlignment] using aligned⟩
  · exact ⟨wf, by simpa only [claimed, memoryAlignment] using aligned⟩
  · exact ⟨wf, by simpa only [claimed, memoryAlignment] using aligned⟩

/-- The branch event keeps the entire signed thirteen-bit Sail immediate. In particular the
compiler does not coerce it through the twelve-bit I-type immediate representation. -/
theorem compileInstructionEvent?_branch_immediate
    {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {imm : BitVec 13} {rs2 rs1 : regidx} {op : bop}
    (decoded : view.decoded = .BTYPE (imm, rs2, rs1, op))
    (routed : view.chipId = .branch)
    (generated : compileInstructionEvent? view frontier clk = some result) :
    ∃ event : ITypeEvent, result.routed = ⟨.branch, event⟩ ∧
      event.imm = (imm.signExtend 64).toNat := by
  rcases view with ⟨pc, word, instruction, key, id, plan⟩
  dsimp only at decoded routed
  subst instruction id
  obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  refine ⟨event, rfl, ?_⟩
  simp only [instructionEventFor?, iTypeEvent?, iOperands?] at constructed
  split at constructed
  · split at constructed
    · cases Option.some.inj constructed
      rfl
    · contradiction
  · contradiction


/-- A compiled JAL uses the decoded sign-extended immediate and incoming PC. -/
theorem compileInstructionEvent?_jal_fields {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {imm : BitVec 21} {rd : regidx}
    (decoded : view.decoded = .JAL (imm, rd)) (routed : view.chipId = .jal)
    (generated : compileInstructionEvent? view frontier clk = some result) :
    ∃ event : JTypeEvent, result.routed = ⟨.jal, event⟩ ∧ event.pc = view.pc.toNat ∧
      event.immB = (imm.signExtend 64).toNat ∧ event.opA = (regidxBits rd).toNat := by
  rcases view with ⟨pc, word, instruction, key, id, plan⟩
  dsimp only at decoded routed
  subst instruction id
  obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  refine ⟨event, rfl, ?_⟩
  simp only [instructionEventFor?, jTypeEvent?] at constructed
  split at constructed
  · split at constructed
    · cases Option.some.inj constructed
      exact ⟨rfl, rfl, rfl⟩
    · contradiction
  · contradiction

private theorem compiled_pulled {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {values : List (BitVec 64)}
    (generated : compileInstructionEvent? view frontier clk = some result) (reads : result.plan.map PlannedTouch.pulled = values) :
    result.stamped.map (fun t => t.touch.pulled) = values := by
  rw [← reads, ← compileInstructionEvent?_stamped_touches generated, List.map_map]
  rfl

/-- A compiled JALR retains the actual base read before any destination write. -/
theorem compileInstructionEvent?_jalr_fields {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {imm : BitVec 12} {rs1 rd : regidx} {base prior : BitVec 64}
    (decoded : view.decoded = .JALR (imm, rs1, rd)) (routed : view.chipId = .jalr)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (reads : result.plan.map PlannedTouch.pulled = [base, prior]) :
    ∃ event : ITypeEvent, result.routed = ⟨.jalr, event⟩ ∧ event.b = base.toNat ∧
      event.imm = (imm.signExtend 64).toNat ∧ event.pc = view.pc.toNat ∧
      event.opA = (regidxBits rd).toNat := by
  have values := compiled_pulled generated reads
  rcases view with ⟨pc, word, instruction, key, id, plan⟩
  dsimp only at decoded routed
  subst instruction id
  obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  refine ⟨event, rfl, ?_⟩
  change (scheduleAccessPlan frontier clk accesses).stampedTouches.map _ = _ at values
  simp only [instructionEventFor?, iTypeEvent?, iOperands?] at constructed
  split at constructed
  · rename_i original b a shape
    split at constructed
    · cases Option.some.inj constructed
      rw [shape] at values
      have first := congrArg List.head? values
      exact ⟨congrArg BitVec.toNat (Option.some.inj first), rfl, rfl, rfl⟩
    · contradiction
  · contradiction

/-- A compiled branch uses both incoming source values, its selected opcode and its complete
thirteen-bit sign-extended offset. -/
theorem compileInstructionEvent?_branch_fields {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {imm : BitVec 13} {rs2 rs1 : regidx} {op : bop} {left right : BitVec 64}
    (decoded : view.decoded = .BTYPE (imm, rs2, rs1, op)) (routed : view.chipId = .branch)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (reads : result.plan.map PlannedTouch.pulled = [right, left]) :
    ∃ event : ITypeEvent, result.routed = ⟨.branch, event⟩ ∧ event.pc = view.pc.toNat ∧
      event.rs1BV = left ∧ event.rs2BV = right ∧ event.imm = (imm.signExtend 64).toNat ∧
      event.opcode = view.routeKey.opcode.toNat := by
  have values := compiled_pulled generated reads
  rcases view with ⟨pc, word, instruction, key, id, plan⟩
  dsimp only at decoded routed
  subst instruction id
  obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  refine ⟨event, rfl, ?_⟩
  change (scheduleAccessPlan frontier clk accesses).stampedTouches.map _ = _ at values
  simp only [instructionEventFor?, iTypeEvent?, iOperands?] at constructed
  split at constructed
  · rename_i original b a shape
    split at constructed
    · cases Option.some.inj constructed
      rw [shape] at values
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at values
      exact ⟨rfl, by simpa [ITypeEvent.rs1BV] using values.2, by simpa [ITypeEvent.rs2BV] using values.1, rfl, rfl⟩
    · contradiction
  · contradiction

private theorem predecessor_register {t : StampedTouch} {slot : AccessSlot} {i : BitVec 5}
    (key : t.touch.operand = (slot, some i)) :
    operandPredecessor t = ⟨i.toNat, t.touch.pulled.toNat, t.previous, true⟩ := by
  have reg := congrArg Prod.snd key
  cases loc : t.touch.loc with
  | reg index =>
    change (match t.touch.loc with | .reg j => some j | .ram _ => none) = some i at reg
    rw [loc] at reg
    cases Option.some.inj reg
    simp [operandPredecessor, loc, MemLoc.busAddress]
  | ram cell => simp [PlannedTouch.operand, loc] at reg

private abbrev OperandsMatch (stamped : List StampedTouch) (decoded : instruction) :=
  stamped.map (fun t => t.touch.operand) = instructionOperands decoded

private theorem cba_operands {decoded : instruction} {c b a : BitVec 5}
    (found : cbaRegisters? decoded = some (c, b, a)) :
    instructionOperands decoded = [(.opC, some c), (.opB, some b), (.opA, some a)] := by
  cases decoded <;> rename_i args <;> cases args <;> simp only [cbaRegisters?, Option.some.injEq, Prod.mk.injEq] at found
  all_goals first | contradiction | obtain ⟨rfl, rfl, rfl⟩ := found; rfl

private theorem rType_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ}
    {e : RTypeEvent} (shape : OperandsMatch stamped decoded) (made : rTypeEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold rTypeEvent? at made
  obtain ⟨⟨ci, bi, ai⟩, regs, made⟩ := Option.bind_eq_some_iff.mp made
  rw [OperandsMatch, cba_operands regs] at shape
  split at made
  · split at made
    · cases made
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
      obtain ⟨c, b, a⟩ := shape
      simp [RTypeEvent.predecessors, predecessor_register c, predecessor_register b, predecessor_register a]
    · contradiction
  · contradiction

private theorem aluReg_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ}
    {e : ALUTypeEvent} (shape : OperandsMatch stamped decoded) (made : aluRegisterEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold aluRegisterEvent? at made
  obtain ⟨⟨ci, bi, ai⟩, regs, made⟩ := Option.bind_eq_some_iff.mp made
  rw [OperandsMatch, cba_operands regs] at shape
  split at made
  · split at made
    · cases made
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
      obtain ⟨c, b, a⟩ := shape
      simp [ALUTypeEvent.predecessors, predecessor_register c, predecessor_register b, predecessor_register a]
    · contradiction
  · contradiction

private theorem aluImm_predecessors {stamped : List StampedTouch} {clk pc opcode : ℕ} {rs1 rd : regidx}
    {imm : BitVec 64} {e : ALUTypeEvent}
    (shape : stamped.map (fun t => t.touch.operand) = [(.opB, some (regidxBits rs1)), (.opA, some (regidxBits rd))])
    (made : aluImmediateEventOf? stamped clk pc opcode rs1 rd imm = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold aluImmediateEventOf? at made
  split at made
  · split at made
    · cases made
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
      simp [ALUTypeEvent.predecessors, predecessor_register shape.1, predecessor_register shape.2]
    · contradiction
  · contradiction

private theorem alu_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ} {e : ALUTypeEvent}
    (shape : OperandsMatch stamped decoded) (made : aluTypeEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold aluTypeEvent? at made
  split at made <;> first | exact aluImm_predecessors shape made | exact aluReg_predecessors shape made

private theorem iInputs_predecessors {width : ℕ} {stamped : List StampedTouch} {clk pc opcode : ℕ} {rs1 rd : regidx}
    {imm : BitVec width} {e : ITypeEvent}
    (shape : stamped.map (fun t => t.touch.operand) = [(.opB, some (regidxBits rs1)), (.opA, some (regidxBits rd))])
    (made : iOperands? stamped clk pc opcode rs1 rd imm = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold iOperands? at made
  split at made
  · split at made
    · cases made
      simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
      simp [ITypeEvent.predecessors, predecessor_register shape.1, predecessor_register shape.2]
    · contradiction
  · contradiction

private theorem iType_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ} {e : ITypeEvent}
    (shape : OperandsMatch stamped decoded) (made : iTypeEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold iTypeEvent? at made
  split at made <;> first | exact iInputs_predecessors shape made | contradiction

private theorem jType_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ} {e : JTypeEvent}
    (shape : OperandsMatch stamped decoded) (made : jTypeEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold jTypeEvent? at made
  split at made
  · split at made
    · split at made <;> cases made
      all_goals
        simp only [OperandsMatch, instructionOperands, List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
        simp [JTypeEvent.predecessors, predecessor_register shape]
    · contradiction
  · contradiction

private def RamOperandsMatch (stamped : List StampedTouch) (decoded : instruction) : Prop :=
  ∀ r ∈ stamped, ∀ b ∈ stamped, r.touch.slot = .ram → b.touch.slot = .opB →
    ∀ imm, ((∃ rs rd width unsigned, decoded = .LOAD (imm, rs, rd, width, unsigned)) ∨
      (∃ rs2 rs1 width, decoded = .STORE (imm, rs2, rs1, width))) →
      r.touch.loc.busAddress = (memoryEffectiveAddress b.touch.pulled imm).toNat / 8 * 8

private theorem ramOperands_of_plan {decoded : instruction} {source target : SailState} {plan : InstructionAccessPlan}
    (made : instructionAccessPlan? decoded source target = some plan) (frontier : AccessFrontier) (base : ℕ) :
    RamOperandsMatch (scheduleAccessPlan frontier base plan).stampedTouches decoded := by
  intro r used b baseMem rSlot bSlot imm memory
  have present (t : StampedTouch) (m : t ∈ (scheduleAccessPlan frontier base plan).stampedTouches) : t.touch ∈ plan :=
    scheduleAccessPlan_erase frontier base plan ▸ List.mem_map_of_mem m
  have kind := (instructionAccessPlan_wellFormed made).locKind _ (present r used)
  cases loc : r.touch.loc with
  | reg i => simp [rSlot, loc, AccessSlot.Accepts] at kind
  | ram cell =>
    have seen : MemLoc.ram cell ∈ plan.map PlannedTouch.loc := loc ▸ List.mem_map_of_mem (present r used)
    have address := instructionAccessPlan_ram made seen
    have read := instructionAccessPlan_memory_base made (present b baseMem) bSlot
    have small (x : BitVec 64) : x.toNat / 8 < 2 ^ 61 := by have := x.isLt; omega
    rcases memory with ⟨rs, rd, width, unsigned, rfl⟩ | ⟨rs2, rs1, width, rfl⟩
    all_goals
      obtain ⟨word, actual, cellEq⟩ := address
      obtain rfl := Option.some.inj (actual.symm.trans read)
      simpa [cellEq, MemLoc.busAddress, memoryRamCell, ramCellOfByteAddress] using small (memoryEffectiveAddress b.touch.pulled imm)

private theorem memory_predecessors {decoded : instruction} {stamped : List StampedTouch} {clk pc opcode : ℕ} {e : MemoryEvent}
    (shape : OperandsMatch stamped decoded) (aligned : RamOperandsMatch stamped decoded)
    (made : memoryEvent? decoded stamped clk pc opcode = some e) :
    e.predecessors = stamped.map operandPredecessor := by
  unfold memoryEvent? at made
  split at made
  · rename_i original ram b a
    split at made
    · rename_i rSlot bSlot aSlot
      have cell := aligned ram (by simp) b (by simp) rSlot bSlot
      split at made <;> cases made
      all_goals
        specialize cell _ (by first | exact Or.inl ⟨_, _, _, _, rfl⟩ | exact Or.inr ⟨_, _, _, rfl⟩)
        simp only [OperandsMatch, instructionOperands, List.map_cons, List.map_nil, List.cons.injEq, and_true] at shape
        rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil,
          predecessor_register shape.2.1, predecessor_register shape.2.2]
        simp only [MemoryEvent.predecessors, ITypeEvent.predecessors, memoryOperands, MemoryEvent.addr, sextNat,
          operandPredecessor, cell, memoryEffectiveAddress, BitVec.toNat_add]
    · contradiction
  · contradiction

/-- The complete predecessors in the native table event are exactly those of the scheduled
Sail plan. This equality preserves order, register aliases, prior words and full timestamps. -/
theorem compileInstructionEvent?_predecessors {program : GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (made : compileInstructionEvent? view frontier clk = some result) :
    result.routed.predecessors = result.stamped.map operandPredecessor := by
  obtain ⟨plan, event, gotPlan, built, rfl⟩ := compileInstructionEvent?_components made
  have generated := (projectSP1Transition?_accesses projected).trans gotPlan
  let stamped := (scheduleAccessPlan frontier clk plan).stampedTouches
  have shape : OperandsMatch stamped view.decoded := by
    change stamped.map (PlannedTouch.operand ∘ StampedTouch.touch) = _
    rw [← List.map_map, scheduleAccessPlan_erase]
    exact instructionAccessPlan_operands generated
  have aligned := ramOperands_of_plan generated frontier clk
  change (RoutedEvent.mk view.chipId event).predecessors = stamped.map operandPredecessor
  generalize idEq : view.chipId = id at event built ⊢
  cases id <;> first
    | exact rType_predecessors shape built
    | exact iType_predecessors shape built
    | exact alu_predecessors shape built
    | exact jType_predecessors shape built
    | exact memory_predecessors shape aligned built

/-- The byte footprint of the four physical store families, before any permission lookups. -/
def RoutedEvent.storeSpan? : RoutedEvent → Option MemorySpan
  | ⟨.storeByte, e⟩ => some ⟨e.addr, 1⟩
  | ⟨.storeHalf, e⟩ => some ⟨e.addr, 2⟩
  | ⟨.storeWord, e⟩ => some ⟨e.addr, 4⟩
  | ⟨.storeDouble, e⟩ => some ⟨e.addr, 8⟩
  | _ => none

private def storeSize : Soundness.Opcode → Option ℕ
  | .SB => some 1 | .SH => some 2 | .SW => some 4 | .SD => some 8 | _ => none

private theorem memoryEvent?_store_avoids {mask : ℕ → Bool} {source : SailState} {decoded : instruction}
    {stamped : List StampedTouch} {clk pc : ℕ} {key : InstructionRouteKey} {e : MemoryEvent} {n : ℕ}
    (keyEq : instructionRouteKey decoded = some key) (image : instructionImageOK decoded = true)
    (checked : InstructionWrite.check mask source.get_reg? decoded = true)
    (baseRead : ∀ t ∈ stamped, t.touch.slot = .opB →
      match (generalizing := false) decoded with
      | .LOAD (_, rs, _, _, _) | .STORE (_, _, rs, _) => source.get_reg? (regidxBits rs) = some t.touch.pulled
      | _ => True)
    (width : storeSize key.opcode = some n)
    (built : memoryEvent? decoded stamped clk pc key.opcode.toNat = some e) : ByteMemory.Avoids mask e.addr n := by
  unfold memoryEvent? at built
  split at built
  · rename_i _ ram b a
    split at built
    · rename_i _ bSlot _
      have observed := baseRead b (by simp) bSlot
      split at built
      next imm rs1 rd unsigned w =>
        cases Option.some.inj keyEq
        have empty : storeSize (loadOpcode w unsigned) = none := by unfold loadOpcode; split_ifs <;> rfl
        rw [empty] at width
        contradiction
      next imm rs2 rs1 w =>
        cases Option.some.inj keyEq
        cases Option.some.inj built
        obtain ⟨value,atBase,allowed⟩ := (InstructionWrite.check_store_iff _ _ _ _ _ _ image).mp checked
        cases Option.some.inj (atBase.symm.trans observed)
        have size : storeSize (storeOpcode w) = some w.toNat := by
          change storeWidthOK w = true at image
          simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at image
          rcases image with ((rfl | rfl) | rfl) | rfl <;> rfl
        obtain rfl := Option.some.inj (size.symm.trans width)
        simpa only [memoryOperands, MemoryEvent.addr, memoryEffectiveAddress, sextNat, BitVec.toNat_add] using allowed
      next => contradiction
    · contradiction
  · contradiction

/-- Every byte requested by the generated store row belongs to the permitted decoded write,
including stores that overwrite the location with its existing value. -/
theorem compileInstructionEvent?_store_avoids {program : GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    {mask : ℕ → Bool} (checked : InstructionWrite.check mask located.source.get_reg? view.decoded = true)
    {span : MemorySpan} (found : result.routed.storeSpan? = some span) : ByteMemory.Avoids mask span.address span.length := by
  obtain ⟨_,keyEq,claimed⟩ := projected_instruction_fields projected
  have plan := compileInstructionEvent?_accessPlan_generated projected generated
  have image := (projectSP1Transition?_components projected).2.2.2.1
  have baseRead := fun (t : StampedTouch) (member : t ∈ result.stamped) (slot : t.touch.slot = .opB) =>
    instructionAccessPlan_memory_base plan
      (show t.touch ∈ result.plan by rw [← compileInstructionEvent?_stamped_touches generated]; exact List.mem_map_of_mem member) slot
  obtain ⟨accesses, event, _, built, rfl⟩ := compileInstructionEvent?_components generated
  generalize eqId : view.chipId = id at event built found claimed
  cases id <;> try contradiction
  all_goals
    cases Option.some.inj found
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds, Bool.and_true,
      List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    exact memoryEvent?_store_avoids keyEq image checked baseRead (by rw [claimed]; rfl) built

end SP1Clean.TraceGen
