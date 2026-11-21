import SP1Clean.Proofs.Completeness.InstructionEvent
import SP1Clean.Proofs.Completeness.StateInventory
import SP1Clean.Semantics.Sail.SailInstructionFrame

/-! # Ordinary compiled State successors and architectural retirement -/

namespace SP1Clean.TraceGen

open Semantics Advance Soundness.Target LeanRV64D

private theorem control_route {decoded : instruction} {id : InstructionChipId}
    (routed : instructionRouteId decoded = some id) (control : ControlFlowInstruction decoded) :
    id ∈ [.jal, .jalr, .branch] := by
  unfold ControlFlowInstruction at control
  split at control
  next operands =>
    obtain ⟨imm, rd⟩ := operands
    have eq : instructionRouteId (.JAL (imm, rd)) = some .jal := by rfl
    cases Option.some.inj (eq.symm.trans routed)
    simp
  next operands =>
    obtain ⟨imm, rs, rd⟩ := operands
    have eq : instructionRouteId (.JALR (imm, rs, rd)) = some .jalr := by rfl
    cases Option.some.inj (eq.symm.trans routed)
    simp
  next operands =>
    obtain ⟨imm, rs2, rs1, op⟩ := operands
    have eq : instructionRouteId (.BTYPE (imm, rs2, rs1, op)) = some .branch := by cases op <;> rfl
    cases Option.some.inj (eq.symm.trans routed)
    simp
  next => contradiction

private theorem normal_straight_pc {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction} {id : InstructionChipId}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (permission : InstructionWrite.PermittedAt readOnly program source)
    (routed : instructionRouteId decoded = some id) (straight : id ∉ [.jal, .jalr, .branch])
    (normal : SailRetiresNormally source target) :
    target.regs.get? Register.PC = some (pc + 4#64) := by
  have notControl (control : ControlFlowInstruction decoded) : False := straight (control_route routed control)
  unfold instructionRouteId at routed
  cases key : instructionRouteKey decoded with
  | none => simp [key] at routed
  | some key' =>
    simp only [instructionRouteKey] at key
    split at key
    all_goals try first
      | exact (arithmetic_normal_successor configured loaded atPc fetched decode trivial normal).1
      | exact (notControl trivial).elim
      | contradiction
    · rename_i imm rs1 rd unsigned width
      rcases rs1 with ⟨rs1⟩
      rcases rd with ⟨rd⟩
      exact (load_normal_successor configured loaded atPc fetched decode normal).1
    · rename_i imm rs2 rs1 width
      rcases rs1 with ⟨rs1⟩
      rcases rs2 with ⟨rs2⟩
      exact (store_normal_successor configured loaded atPc fetched decode permission normal).1

/-- The actual compiled receipt of each of the 22 straight-line routes encodes the full Sail
successor PC, even where adding four carries out of its low limb. -/
theorem compileInstructionEvent?_straight_successor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    {view : SP1TransitionView} {result : CompiledInstructionEvent} {frontier : AccessFrontier} {clk : ℕ}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : InstructionWrite.PermittedAt readOnly program source) (normal : SailRetiresNormally source target)
    (projected : projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (straight : result.routed.id ∉ [.jal, .jalr, .branch]) :
    target.regs.get? Register.PC = some (StateMsg.pcBits (result.routed.rawPushState.toMessage (p := p))) := by
  have component := projectSP1Transition?_components projected
  obtain ⟨pc, word, decoded, src, fetched, decode, checked⟩ := permission
  have same := decodeLocated?_eq_some_of (located := ⟨source, ⟨.ordinary, target⟩⟩) src fetched (decode source configured)
  obtain rfl : pc = view.pc := Option.some.inj (src.symm.trans component.1)
  obtain rfl : word = view.word := Option.some.inj (fetched.symm.trans component.2.1)
  obtain rfl : decoded = view.decoded := Option.some.inj (same.symm.trans component.2.2.1)
  have routed := compileInstructionEvent?_route generated
  have value := normal_straight_pc configured loaded src fetched decode ⟨_, _, _, src, fetched, decode, checked⟩
    (projectSP1Transition?_route projected) (routed ▸ straight) normal
  have bounded : view.pc.toNat < 2 ^ 48 := by
    obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
    have equal : entry.1 = view.pc := by simpa only [beq_iff_eq] using List.find?_some found
    have window := program.rom_in_window entry (List.mem_of_find?_eq_some found)
    rw [equal] at window
    omega
  have coord := (compileInstructionEvent?_coordinates generated).2
  rw [value, Option.some.injEq, RoutedEvent.rawPushState_pcBits]
  rcases result with ⟨⟨id, event⟩, plan, schedule⟩
  change id ∉ [.jal, .jalr, .branch] at straight
  cases id
  case jal => exact (straight (by simp)).elim
  case jalr => exact (straight (by simp)).elim
  case branch => exact (straight (by simp)).elim
  all_goals
    change _ = BitVec.ofNat 64 (_ % 2 ^ 48 + 4)
    rw [coord, Nat.mod_eq_of_lt bounded]
    rfl

private theorem projected_configured_decode {readOnly : ℕ → Bool} {program : GuestProgram}
    {source : SailState} {step : Machine.EventTransition} {view : SP1TransitionView}
    (configured : SailConfigured source) (permission : InstructionWrite.PermittedAt readOnly program source)
    (projected : projectSP1Transition? program ⟨source, step⟩ = some view) :
    ConfiguredDecode view.word view.decoded := by
  have component := projectSP1Transition?_components projected
  obtain ⟨pc, word, decoded, src, fetched, decode, _⟩ := permission
  have same := decodeLocated?_eq_some_of (located := ⟨source, step⟩) src fetched (decode source configured)
  obtain rfl : pc = view.pc := Option.some.inj (src.symm.trans component.1)
  obtain rfl : word = view.word := Option.some.inj (fetched.symm.trans component.2.1)
  obtain rfl : decoded = view.decoded := Option.some.inj (same.symm.trans component.2.2.1)
  exact decode

private theorem emitted_bounded_pc {target : SailState} {pc : BitVec 64} {n : ℕ}
    (arrived : target.regs.get? Register.PC = some pc) (value : n = pc.toNat)
    (bounded : ∀ dest, target.regs.get? Register.PC = some dest → dest.toNat < 2 ^ 48) :
    target.regs.get? Register.PC = some (BitVec.ofNat 64 (n % 2 ^ 48)) := by
  rw [value, Nat.mod_eq_of_lt (bounded pc arrived), BitVec.ofNat_toNat, BitVec.setWidth_eq, arrived]

private theorem cleared_target (bits : BitVec 64) :
    bits.toNat - bits.toNat % 2 = (Sail.BitVec.update bits 0 0#1).toNat := by
  have h := ofNat64_clear_lsb_and (M := bits.toNat - bits.toNat % 2) (b := bits.toNat % 2) (by omega) (by omega)
  rw [show bits.toNat - bits.toNat % 2 + bits.toNat % 2 = bits.toNat by omega, BitVec.ofNat_toNat] at h
  have same : BitVec.ofNat 64 (bits.toNat - bits.toNat % 2) = Sail.BitVec.update bits 0 0#1 := by
    simpa [Sail.BitVec.update, Sail.BitVec.updateSubrange'] using h
  have equal := congrArg BitVec.toNat same
  rwa [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := bits.isLt; omega)] at equal

private theorem branch_taken {e : ITypeEvent} {op : bop} {left right : BitVec 64}
    (code : e.opcode = (bopToOpcode op).toNat) (rs1 : e.rs1BV = left) (rs2 : e.rs2BV = right) :
    e.branchTaken = true ↔ BranchSail.branchCond op left right := by
  cases op <;> simp [ITypeEvent.branchTaken, code, bopToOpcode, Soundness.Opcode.toNat, rs1, rs2, BranchSail.branchCond]

private theorem compiled_jal_successor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {program : GuestProgram} {source target : SailState} {view : SP1TransitionView}
    {result : CompiledInstructionEvent} {frontier : AccessFrontier} {clk : ℕ} {imm : BitVec 21} {rd : BitVec 5}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (decoded : view.decoded = .JAL (imm, .Regidx rd))
    (decode : ConfiguredDecode view.word view.decoded) (normal : SailRetiresNormally source target)
    (projected : projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : ∀ dest, target.regs.get? Register.PC = some dest → dest.toNat < 2 ^ 48) :
    target.regs.get? Register.PC = some (StateMsg.pcBits (result.routed.rawPushState.toMessage (p := p))) := by
  have c := projectSP1Transition?_components projected
  have route := projectSP1Transition?_route projected
  rw [decoded] at decode route
  have selected : view.chipId = .jal := Option.some.inj route.symm
  obtain ⟨e, same, pc, offset⟩ := compileInstructionEvent?_jal_fields decoded selected generated
  have arrived := jal_normal_successor configured loaded c.1 c.2.1 decode normal
  rw [same, RoutedEvent.rawPushState_pcBits]
  apply emitted_bounded_pc arrived _ bounded
  simp only [JTypeEvent.jalTarget, pc, offset, BitVec.toNat_add]
  rfl

private theorem compiled_jalr_successor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {program : GuestProgram} {source target : SailState} {view : SP1TransitionView}
    {result : CompiledInstructionEvent} {frontier : AccessFrontier} {clk : ℕ} {imm : BitVec 12} {rs1 rd : BitVec 5}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (decoded : view.decoded = .JALR (imm, .Regidx rs1, .Regidx rd))
    (decode : ConfiguredDecode view.word view.decoded) (normal : SailRetiresNormally source target)
    (projected : projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : ∀ dest, target.regs.get? Register.PC = some dest → dest.toNat < 2 ^ 48) :
    target.regs.get? Register.PC = some (StateMsg.pcBits (result.routed.rawPushState.toMessage (p := p))) := by
  have c := projectSP1Transition?_components projected
  have route := projectSP1Transition?_route projected
  have plan := compileInstructionEvent?_accessPlan_generated projected generated
  rw [decoded] at decode route plan
  have selected : view.chipId = .jalr := Option.some.inj route.symm
  obtain ⟨base, baseRead⟩ := initialized_gpr source configured.init rs1
  obtain ⟨prior, priorRead⟩ := initialized_gpr source configured.init rd
  have reads := jalrPlan_pulled (rs1 := .Regidx rs1) (rd := .Regidx rd) baseRead priorRead plan
  obtain ⟨e, same, sourceB, offset⟩ := compileInstructionEvent?_jalr_fields decoded selected generated reads
  have arrived := jalr_normal_successor configured loaded c.1 c.2.1 baseRead decode normal
  rw [same, RoutedEvent.rawPushState_pcBits]
  apply emitted_bounded_pc arrived _ bounded
  have add : e.jalrTarget = (base + imm.signExtend 64).toNat := by
    simp only [ITypeEvent.jalrTarget, sourceB, offset, BitVec.toNat_add]
  rw [add]
  exact cleared_target _

private theorem compiled_branch_successor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {program : GuestProgram} {source target : SailState} {view : SP1TransitionView}
    {result : CompiledInstructionEvent} {frontier : AccessFrontier} {clk : ℕ} {imm : BitVec 13} {rs1 rs2 : BitVec 5} {op : bop}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (decoded : view.decoded = .BTYPE (imm, .Regidx rs2, .Regidx rs1, op))
    (decode : ConfiguredDecode view.word view.decoded) (normal : SailRetiresNormally source target)
    (projected : projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : ∀ dest, target.regs.get? Register.PC = some dest → dest.toNat < 2 ^ 48) :
    target.regs.get? Register.PC = some (StateMsg.pcBits (result.routed.rawPushState.toMessage (p := p))) := by
  have c := projectSP1Transition?_components projected
  have route := projectSP1Transition?_route projected
  have key := c.2.2.2.2.1
  have plan := compileInstructionEvent?_accessPlan_generated projected generated
  rw [decoded] at decode route plan key
  have selected : view.chipId = .branch := by
    cases op <;> exact Option.some.inj route.symm
  have opEq : view.routeKey.opcode = bopToOpcode op := congrArg InstructionRouteKey.opcode (Option.some.inj key.symm)
  obtain ⟨left, leftRead⟩ := initialized_gpr source configured.init rs1
  obtain ⟨right, rightRead⟩ := initialized_gpr source configured.init rs2
  have reads := branchPlan_pulled (rs1 := .Regidx rs1) (rs2 := .Regidx rs2) leftRead rightRead plan
  obtain ⟨e, same, pc, rs1Val, rs2Val, offset, opcode⟩ := compileInstructionEvent?_branch_fields decoded selected generated reads
  have decision := branch_taken (opcode.trans (congrArg Soundness.Opcode.toNat opEq)) rs1Val rs2Val
  have next := branch_normal_successor configured loaded c.1 c.2.1 leftRead rightRead decode normal
  rw [same, RoutedEvent.rawPushState_pcBits]
  cases hb : e.branchTaken with
  | true =>
    apply emitted_bounded_pc (next.1 (decision.mp hb)) _ bounded
    simp only [ITypeEvent.branchNextPc, hb, ↓reduceIte, ITypeEvent.branchTarget, pc, offset, BitVec.toNat_add]
    rfl
  | false =>
    have untaken : ¬ BranchSail.branchCond op left right := fun h => by simp [hb] at decision; exact decision h
    apply emitted_bounded_pc (next.2 untaken) _ bounded
    simp [ITypeEvent.branchNextPc, hb, pc, BitVec.toNat_add]

private def isControlOpcode : Soundness.Opcode → Bool
  | .JAL | .JALR | .BEQ | .BNE | .BLT | .BGE | .BLTU | .BGEU => true
  | _ => false

private theorem control_of_route {decoded : instruction} {key : InstructionRouteKey} {id : InstructionChipId}
    (keyEq : instructionRouteKey decoded = some key) (route : instructionRouteId decoded = some id)
    (selected : id ∈ [.jal, .jalr, .branch]) : ControlFlowInstruction decoded := by
  have table : ∀ (op : Soundness.Opcode) (zero : Bool), (routeId op zero).any
     (fun i => [InstructionChipId.jal, .jalr, .branch].contains i) = isControlOpcode op := by
    intro op zero
    cases op <;> cases zero <;> rfl
  unfold instructionRouteId at route
  rw [keyEq, Option.bind_some] at route
  have belongs := table key.opcode key.opAIsX0
  rw [route, Option.any_some] at belongs
  have opcode : isControlOpcode key.opcode = true := belongs.symm.trans (List.contains_iff_mem.mpr selected)
  have noLoad (width : word_width) (signed : Bool) : isControlOpcode (loadOpcode width signed) = false := by
    by_cases one : width = 1 <;> by_cases two : width = 2 <;> by_cases four : width = 4 <;>
      cases signed <;> simp [loadOpcode, one, two, four, isControlOpcode]
  have noStore (width : word_width) : isControlOpcode (storeOpcode width) = false := by
    by_cases one : width = 1 <;> by_cases two : width = 2 <;> by_cases four : width = 4 <;>
      simp [storeOpcode, one, two, four, isControlOpcode]
  simp only [instructionRouteKey] at keyEq
  split at keyEq
  all_goals try first | exact trivial | contradiction
  all_goals cases Option.some.inj keyEq
  all_goals try contradiction
  all_goals try solve | rw [noLoad] at opcode; contradiction
  all_goals try solve | rw [noStore] at opcode; contradiction
  all_goals rename_i op
  all_goals first
    | cases op <;> contradiction
    | rcases op with ⟨part, signed1, signed2⟩
      cases part <;> cases signed1 <;> cases signed2 <;> contradiction

/-- Every ordinary producer's raw State receipt encodes the actual committed architectural
successor at a representable endpoint. Only the destination the interpreter actually reaches
must fit; unused fall-through and branch addresses are unrestricted. -/
theorem compileInstructionEvent?_successor {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
    {readOnly : ℕ → Bool} {program : GuestProgram} {source target : SailState}
    {view : SP1TransitionView} {result : CompiledInstructionEvent} {frontier : AccessFrontier} {clk : ℕ}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (permission : InstructionWrite.PermittedAt readOnly program source) (normal : SailRetiresNormally source target)
    (projected : projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : ∀ dest, target.regs.get? Register.PC = some dest → dest.toNat < 2 ^ 48) :
    target.regs.get? Register.PC = some (StateMsg.pcBits (result.routed.rawPushState.toMessage (p := p))) := by
  by_cases selected : result.routed.id ∈ [.jal, .jalr, .branch]
  · have decode := projected_configured_decode configured permission projected
    have control := control_of_route (projectSP1Transition?_components projected).2.2.2.2.1
      (projectSP1Transition?_route projected) (compileInstructionEvent?_route generated ▸ selected)
    unfold ControlFlowInstruction at control
    split at control
    next operands eq =>
      obtain ⟨imm, ⟨rd⟩⟩ := operands
      exact compiled_jal_successor configured loaded eq decode normal projected generated bounded
    next operands eq =>
      obtain ⟨imm, ⟨rs1⟩, ⟨rd⟩⟩ := operands
      exact compiled_jalr_successor configured loaded eq decode normal projected generated bounded
    next operands eq =>
      obtain ⟨imm, ⟨rs2⟩, ⟨rs1⟩, op⟩ := operands
      exact compiled_branch_successor configured loaded eq decode normal projected generated bounded
    next => contradiction
  · exact compileInstructionEvent?_straight_successor configured loaded permission normal projected generated selected

end SP1Clean.TraceGen
