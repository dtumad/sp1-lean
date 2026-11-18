import SP1Clean.Semantics.ISA.Opcode
import SP1Clean.Semantics.ISA.Decode
import SP1Clean.Semantics.Execution.ConfiguredState
import SP1Clean.Proofs.Sail.InstructionDecode

/-! # Concrete `decodedInROM` examples, one per supported instruction family

Each example is a one-instruction guest program at pc `0x10000`, the committed Program-bus row it
decodes to, and a proof of `decodedInROM` for that pair. The fetch reduces at the singleton ROM
(`pcBitsOfRow_x10000` keys it at `0x10000`); the configured-state decode is
`SailDecode.instructionDecode_agrees` at the executable decoder's result, checked by `rfl`; and the
`instrToProgramRow'` projection closes by `rfl` against the transcribed row. A mis-transcribed
`instrToProgramRow` arm breaks its family's example, so `decodedInROM` cannot become silently
vacuous for that family.
-/

open LeanRV64D
namespace SP1CleanTest.ProgramDecode

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean SP1Clean.Semantics SP1Clean.Soundness SP1Clean.Soundness.Target
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## The R-type example -/


/-- A one-instruction guest program: `ADD x1, x2, x3` (`0x003100B3`) at pc `0x10000` — the base of the SP1
code window `[2^16, 2^48)`, so it satisfies `rom_in_window`; the word's low two bits are `0b11`
(non-compressed), so it satisfies `rom_full_width`. Doubles as the pilot's end-to-end `advance` witness. -/
def addProgram : GuestProgram where
  rom := [(0x10000#64, 0x003100B3#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed Program-bus row the ADD decodes to — the `instrToProgramRow` projection at pc `0x10000`
(`op_a = rd = x1`, `op_b[0] = rs1 = x2`, `op_c[0] = rs2 = x3`, opcode `ADD`; `pc1 = 1` for `0x10000`). -/
def addRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((ropToOpcode rop.ADD).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-! ## The other families -/


/-- Any committed row with pc limbs `(0, 1, 0)` keys the ROM at `0x10000` — the shared
`pcBitsOfRow` computation of every example row. Not a `rfl`: the pc-limb casts sit under
`ZMod.val` at a symbolic `p`, so the limbs are lifted by `ZMod.val_natCast_of_lt` first. -/
private theorem pcBitsOfRow_x10000 (row : ProgramRow (ZMod p)) (h0 : row.pc0 = 0)
    (h1 : row.pc1 = 1) (h2 : row.pc2 = 0) : pcBitsOfRow row = 0x10000#64 := by
  have hp : (2 : ℕ) ^ 24 < p := Fact.out
  have h0v : ((0 : ZMod p)).val = 0 := by
    rw [← Nat.cast_zero (R := ZMod p), ZMod.val_natCast_of_lt (by omega)]
  have h1v : ((1 : ZMod p)).val = 1 := by
    rw [← Nat.cast_one (R := ZMod p), ZMod.val_natCast_of_lt (by omega)]
  simp only [pcBitsOfRow, pcBitsOfVals, h0, h1, h2, h0v, h1v]
  rfl

/-- End-to-end R-type example: the one-ADD program's committed row is `decodedInROM`. -/
theorem decodedInROM_addRow : decodedInROM addProgram (addRow (p := p)) := by
  refine ⟨0x003100B3#32,
    .RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `ADDI x1, x2, 5` (`0x00510093`) at pc `0x10000` — the I-type example program. -/
def addiProgram : GuestProgram where
  rom := [(0x10000#64, 0x00510093#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `addiProgram` decodes to — the `instrToProgramRow` I-type arm at pc
`#v[0, 1, 0]`. -/
def addiRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((iopToOpcode iop.ADDI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((5#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end I-type example. -/
theorem decodedInROM_addiRow : decodedInROM addiProgram (addiRow (p := p)) := by
  refine ⟨0x00510093#32,
    .ITYPE (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5, iop.ADDI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addiRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `SLLI x1, x2, 3` (`0x00311093`) at pc `0x10000` — the shift-immediate example program. -/
def slliProgram : GuestProgram where
  rom := [(0x10000#64, 0x00311093#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `slliProgram` decodes to — the SHIFTIOP arm (zero-extended shift amount). -/
def slliRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((sopToOpcode sop.SLLI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((3#6).setWidth 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end shift-immediate example. -/
theorem decodedInROM_slliRow : decodedInROM slliProgram (slliRow (p := p)) := by
  refine ⟨0x00311093#32,
    .SHIFTIOP (3#6, regidx.Regidx 2#5, regidx.Regidx 1#5, sop.SLLI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (slliRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `ADDIW x1, x2, 5` (`0x0051009B`) at pc `0x10000` — the W-form I-type example program. -/
def addiwProgram : GuestProgram where
  rom := [(0x10000#64, 0x0051009B#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `addiwProgram` decodes to — the ADDIW arm (opcode ADDW, `imm_c = 1`). -/
def addiwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.ADDW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((5#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end ADDIW example. -/
theorem decodedInROM_addiwRow : decodedInROM addiwProgram (addiwRow (p := p)) := by
  refine ⟨0x0051009B#32, .ADDIW (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addiwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `ADDW x1, x2, x3` (`0x003100BB`) at pc `0x10000` — the W-form R-type example program. -/
def addwProgram : GuestProgram where
  rom := [(0x10000#64, 0x003100BB#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `addwProgram` decodes to — the RTYPEW arm. -/
def addwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((ropwToOpcode ropw.ADDW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end RTYPEW example. -/
theorem decodedInROM_addwRow : decodedInROM addwProgram (addwRow (p := p)) := by
  refine ⟨0x003100BB#32,
    .RTYPEW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, ropw.ADDW), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (addwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `SLLIW x1, x2, 3` (`0x0031109B`) at pc `0x10000` — the W-form shift-immediate example
program. -/
def slliwProgram : GuestProgram where
  rom := [(0x10000#64, 0x0031109B#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `slliwProgram` decodes to — the SHIFTIWOP arm (5-bit shift amount). -/
def slliwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((sopwToOpcode sopw.SLLIW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((3#5).setWidth 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end word shift-immediate example. -/
theorem decodedInROM_slliwRow : decodedInROM slliwProgram (slliwRow (p := p)) := by
  refine ⟨0x0031109B#32,
    .SHIFTIWOP (3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, sopw.SLLIW), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (slliwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `LUI x1, 1` (`0x000010B7`) at pc `0x10000` — the U-type example program. -/
def luiProgram : GuestProgram where
  rom := [(0x10000#64, 0x000010B7#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `luiProgram` decodes to — the UTYPE arm (`op_b = op_c` the shifted
immediate, both immediate flags set). -/
def luiRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((uopToOpcode uop.LUI).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := bitVecToWord (((1#20).signExtend 64) <<< 12),
    imm_b := 1,
    op_c := bitVecToWord (((1#20).signExtend 64) <<< 12),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end U-type example. -/
theorem decodedInROM_luiRow : decodedInROM luiProgram (luiRow (p := p)) := by
  refine ⟨0x000010B7#32, .UTYPE (1#20, regidx.Regidx 1#5, uop.LUI), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (luiRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `JAL x1, 8` (`0x008000EF`) at pc `0x10000` — the J-type example program. -/
def jalProgram : GuestProgram where
  rom := [(0x10000#64, 0x008000EF#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `jalProgram` decodes to — the JAL arm (`op_b` the sign-extended offset,
`op_c = 0`). -/
def jalRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.JAL).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := bitVecToWord ((8#21).signExtend 64),
    imm_b := 1,
    op_c := #v[0, 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end JAL example. -/
theorem decodedInROM_jalRow : decodedInROM jalProgram (jalRow (p := p)) := by
  refine ⟨0x008000EF#32, .JAL (8#21, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (jalRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `JALR x1, x2, 4` (`0x004100E7`) at pc `0x10000` — the JALR example program. -/
def jalrProgram : GuestProgram where
  rom := [(0x10000#64, 0x004100E7#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `jalrProgram` decodes to — the JALR arm (I-type shape). -/
def jalrRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.JALR).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((4#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end JALR example. -/
theorem decodedInROM_jalrRow : decodedInROM jalrProgram (jalrRow (p := p)) := by
  refine ⟨0x004100E7#32, .JALR (4#12, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (jalrRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `BEQ x1, x2, 8` (`0x00208463`) at pc `0x10000` — the B-type example program. -/
def beqProgram : GuestProgram where
  rom := [(0x10000#64, 0x00208463#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `beqProgram` decodes to — the BTYPE arm (`op_a = rs1`, a source; `op_c` the
sign-extended offset). -/
def beqRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((bopToOpcode bop.BEQ).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((8#13).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end B-type example. -/
theorem decodedInROM_beqRow : decodedInROM beqProgram (beqRow (p := p)) := by
  refine ⟨0x00208463#32,
    .BTYPE (8#13, regidx.Regidx 2#5, regidx.Regidx 1#5, bop.BEQ), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (beqRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `LW x1, 0(x2)` (`0x00012083`) at pc `0x10000` — the LOAD example program. -/
def lwProgram : GuestProgram where
  rom := [(0x10000#64, 0x00012083#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `lwProgram` decodes to — the LOAD arm at width 4, signed (the
`loadWidthOK`-guarded projection accepts it). -/
def lwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((loadOpcode 4 false).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((0#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end LOAD example (width 4 — the `LW` opcode). -/
theorem decodedInROM_lwRow : decodedInROM lwProgram (lwRow (p := p)) := by
  refine ⟨0x00012083#32,
    .LOAD (0#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 4), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (lwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `SW x1, 0(x2)` (`0x00112023`) at pc `0x10000` — the STORE example program. -/
def swProgram : GuestProgram where
  rom := [(0x10000#64, 0x00112023#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `swProgram` decodes to — the STORE arm at width 4 (`op_a = rs2`, the value
source; the `storeWidthOK`-guarded projection accepts it). -/
def swRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((storeOpcode 4).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := bitVecToWord ((0#12).signExtend 64),
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 1 }

/-- End-to-end STORE example (width 4 — the `SW` opcode). -/
theorem decodedInROM_swRow : decodedInROM swProgram (swRow (p := p)) := by
  refine ⟨0x00112023#32,
    .STORE (0#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 4), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (swRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `MUL x1, x2, x3` (`0x023100B3`) at pc `0x10000` — the M-extension multiply example program. -/
def mulProgram : GuestProgram where
  rom := [(0x10000#64, 0x023100B3#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `mulProgram` decodes to — the MUL arm at the canonical
`(Low, Signed, Signed)` descriptor (the `mulOpCanonical`-guarded projection accepts it). -/
def mulRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((mulOpToOpcode ⟨.Low, .Signed, .Signed⟩).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end MUL example (the M families additionally consume `SailConfigured.misa_m`). -/
theorem decodedInROM_mulRow : decodedInROM mulProgram (mulRow (p := p)) := by
  refine ⟨0x023100B3#32,
    .MUL (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, ⟨.Low, .Signed, .Signed⟩),
    ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (mulRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `MULW x1, x2, x3` (`0x023100BB`) at pc `0x10000` — the MULW example program. -/
def mulwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023100BB#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `mulwProgram` decodes to — the MULW arm. -/
def mulwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.MULW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end MULW example. -/
theorem decodedInROM_mulwRow : decodedInROM mulwProgram (mulwRow (p := p)) := by
  refine ⟨0x023100BB#32,
    .MULW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (mulwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `DIV x1, x2, x3` (`0x023140B3`) at pc `0x10000` — the signed-divide example program. -/
def divProgram : GuestProgram where
  rom := [(0x10000#64, 0x023140B3#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `divProgram` decodes to — the DIV arm at `isU = false` (opcode DIV). -/
def divRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.DIV).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end DIV example. -/
theorem decodedInROM_divRow : decodedInROM divProgram (divRow (p := p)) := by
  refine ⟨0x023140B3#32,
    .DIV (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (divRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `REM x1, x2, x3` (`0x023160B3`) at pc `0x10000` — the signed-remainder example program. -/
def remProgram : GuestProgram where
  rom := [(0x10000#64, 0x023160B3#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `remProgram` decodes to — the REM arm at `isU = false` (opcode REM). -/
def remRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.REM).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end REM example. -/
theorem decodedInROM_remRow : decodedInROM remProgram (remRow (p := p)) := by
  refine ⟨0x023160B3#32,
    .REM (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (remRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `DIVW x1, x2, x3` (`0x023140BB`) at pc `0x10000` — the W-form signed-divide example
program. -/
def divwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023140BB#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `divwProgram` decodes to — the DIVW arm at `isU = false` (opcode DIVW). -/
def divwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.DIVW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end DIVW example. -/
theorem decodedInROM_divwRow : decodedInROM divwProgram (divwRow (p := p)) := by
  refine ⟨0x023140BB#32,
    .DIVW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (divwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

/-- `REMW x1, x2, x3` (`0x023160BB`) at pc `0x10000` — the W-form signed-remainder example
program. -/
def remwProgram : GuestProgram where
  rom := [(0x10000#64, 0x023160BB#32)]
  pc_start := 0x10000#64
  memImage := []
  rom_nodup := by simp
  rom_aligned := by
    intro a ha; simp only [List.map_cons, List.map_nil, List.mem_singleton] at ha; subst ha
    norm_num [BitVec.toNat_ofNat]
  rom_in_window := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha
    refine ⟨?_, ?_⟩ <;> norm_num [BitVec.toNat_ofNat]
  rom_full_width := by
    intro aw ha; simp only [List.mem_singleton] at ha; subst ha; decide

/-- The committed row `remwProgram` decodes to — the REMW arm at `isU = false` (opcode REMW). -/
def remwRow : ProgramRow (ZMod p) :=
  { pc0 := 0, pc1 := 1, pc2 := 0,
    opcode := ((Opcode.REMW).toNat : ZMod p),
    op_a := regidxVal (regidx.Regidx 1#5),
    op_b := #v[regidxVal (regidx.Regidx 2#5), 0, 0, 0],
    imm_b := 0,
    op_c := #v[regidxVal (regidx.Regidx 3#5), 0, 0, 0],
    op_a_0 := if regidxVal (p := p) (regidx.Regidx 1#5) = 0 then 1 else 0,
    imm_c := 0 }

/-- End-to-end REMW example. -/
theorem decodedInROM_remwRow : decodedInROM remwProgram (remwRow (p := p)) := by
  refine ⟨0x023160BB#32,
    .REMW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false), ?_, ?_, ?_⟩
  · rw [pcBitsOfRow_x10000 (remwRow (p := p)) rfl rfl rfl]; rfl
  · intro s hcfg
    exact SailDecode.instructionDecode_agrees _ _ rfl s hcfg
  · rfl

end SP1CleanTest.ProgramDecode
