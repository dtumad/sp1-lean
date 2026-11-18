module

public import LeanRV64D.InstsEnd

/-! # Per-instruction dispatch of the Sail `execute` function

`LeanRV64D.Functions.execute` is one match with an alternative for every instruction. Unfolding it
with `simp only [execute]` makes Lean generate its equation lemmas and their match splitter in the
current module. The splitter is a private definition that is also compiled to native code (two
functions of about 80,000 lines of C each), and every module that unfolds `execute` regenerates it.

Each equation below selects one alternative definitionally, without generating either, so proofs
rewrite with these instead of unfolding `execute`.
-/

public section

namespace SP1Clean.SailExecute
open LeanRV64D LeanRV64D.Functions

theorem dispatch_UTYPE (imm rd op) : execute (.UTYPE (imm, rd, op)) = execute_UTYPE imm rd op := rfl
theorem dispatch_JAL (imm rd) : execute (.JAL (imm, rd)) = execute_JAL imm rd := rfl
theorem dispatch_JALR (imm rs1 rd) : execute (.JALR (imm, rs1, rd)) = execute_JALR imm rs1 rd := rfl
theorem dispatch_BTYPE (imm rs2 rs1 op) :
    execute (.BTYPE (imm, rs2, rs1, op)) = execute_BTYPE imm rs2 rs1 op := rfl
theorem dispatch_ITYPE (imm rs1 rd op) :
    execute (.ITYPE (imm, rs1, rd, op)) = execute_ITYPE imm rs1 rd op := rfl
theorem dispatch_SHIFTIOP (shamt rs1 rd op) :
    execute (.SHIFTIOP (shamt, rs1, rd, op)) = execute_SHIFTIOP shamt rs1 rd op := rfl
theorem dispatch_RTYPE (rs2 rs1 rd op) :
    execute (.RTYPE (rs2, rs1, rd, op)) = execute_RTYPE rs2 rs1 rd op := rfl
theorem dispatch_LOAD (imm rs1 rd unsigned width) :
    execute (.LOAD (imm, rs1, rd, unsigned, width)) = execute_LOAD imm rs1 rd unsigned width := rfl
theorem dispatch_STORE (imm rs2 rs1 width) :
    execute (.STORE (imm, rs2, rs1, width)) = execute_STORE imm rs2 rs1 width := rfl
theorem dispatch_ADDIW (imm rs1 rd) : execute (.ADDIW (imm, rs1, rd)) = execute_ADDIW imm rs1 rd := rfl
theorem dispatch_RTYPEW (rs2 rs1 rd op) :
    execute (.RTYPEW (rs2, rs1, rd, op)) = execute_RTYPEW rs2 rs1 rd op := rfl
theorem dispatch_SHIFTIWOP (shamt rs1 rd op) :
    execute (.SHIFTIWOP (shamt, rs1, rd, op)) = execute_SHIFTIWOP shamt rs1 rd op := rfl
theorem dispatch_MUL (rs2 rs1 rd op) : execute (.MUL (rs2, rs1, rd, op)) = execute_MUL rs2 rs1 rd op :=
  rfl
theorem dispatch_DIV (rs2 rs1 rd unsigned) :
    execute (.DIV (rs2, rs1, rd, unsigned)) = execute_DIV rs2 rs1 rd unsigned := rfl
theorem dispatch_REM (rs2 rs1 rd unsigned) :
    execute (.REM (rs2, rs1, rd, unsigned)) = execute_REM rs2 rs1 rd unsigned := rfl
theorem dispatch_MULW (rs2 rs1 rd) : execute (.MULW (rs2, rs1, rd)) = execute_MULW rs2 rs1 rd := rfl
theorem dispatch_DIVW (rs2 rs1 rd unsigned) :
    execute (.DIVW (rs2, rs1, rd, unsigned)) = execute_DIVW rs2 rs1 rd unsigned := rfl
theorem dispatch_REMW (rs2 rs1 rd unsigned) :
    execute (.REMW (rs2, rs1, rd, unsigned)) = execute_REMW rs2 rs1 rd unsigned := rfl

end SP1Clean.SailExecute
