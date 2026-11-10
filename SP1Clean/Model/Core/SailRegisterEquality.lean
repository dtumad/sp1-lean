import SP1Clean.Model.Register
import ToMathlib.DeriveDecidableEq

/-! # Exact executable comparison of the complete Sail register file

These instances prove the generated register-value comparisons lawful and provide executable
structural equality for the decoded instructions retained by waiting harts.
The resulting finite-map comparison includes platform registers, nextPC, retirement bookkeeping,
and absent keys; it does not identify states merely because their integer registers agree.
-/

namespace SP1Clean.Model.Core

open LeanRV64D

-- Waiting harts retain the full decoded instruction. Compare it structurally, including
-- alternatives outside SP1's profile; arbitrary initialized states may contain them.
-- Standalone `deriving instance` cannot choose instance names, and Sail's type names use
-- underscores. Reuse Lean's structural-equality deriver with explicit camel-case names;
-- the constructor comparisons and their kernel-checked proofs remain the standard derivation.
open Lean Elab Command Deriving in
run_cmd do
  for typeName in #[``LeanRV64D.vregidx, ``LeanRV64D.Signedness, ``LeanRV64D.VectorHalf, ``LeanRV64D.amoop,
    ``LeanRV64D.cbop_zicbom, ``LeanRV64D.cbop_zicbop, ``LeanRV64D.biop, ``LeanRV64D.bop, ``LeanRV64D.fregidx,
    ``LeanRV64D.cfregidx, ``LeanRV64D.cregidx, ``LeanRV64D.csrop, ``LeanRV64D.f_bin_f_op_D,
    ``LeanRV64D.f_bin_f_op_H, ``LeanRV64D.f_bin_rm_op_D, ``LeanRV64D.f_bin_rm_op_H,
    ``LeanRV64D.f_bin_rm_op_S, ``LeanRV64D.f_bin_op_f_S, ``LeanRV64D.f_bin_op_x_S, ``LeanRV64D.f_bin_x_op_D,
    ``LeanRV64D.f_bin_x_op_H, ``LeanRV64D.f_madd_op_D, ``LeanRV64D.f_madd_op_H, ``LeanRV64D.f_madd_op_S,
    ``LeanRV64D.f_un_f_op_D, ``LeanRV64D.f_un_f_op_H, ``LeanRV64D.f_un_rm_ff_op_D,
    ``LeanRV64D.f_un_rm_ff_op_H, ``LeanRV64D.f_un_rm_fx_op_D, ``LeanRV64D.f_un_rm_fx_op_H,
    ``LeanRV64D.f_un_rm_fx_op_S, ``LeanRV64D.f_un_rm_xf_op_D, ``LeanRV64D.f_un_rm_xf_op_H,
    ``LeanRV64D.f_un_rm_xf_op_S, ``LeanRV64D.f_un_op_f_S, ``LeanRV64D.f_un_op_x_S, ``LeanRV64D.f_un_x_op_D,
    ``LeanRV64D.f_un_x_op_H, ``LeanRV64D.rounding_mode, ``LeanRV64D.fvfmafunct6, ``LeanRV64D.fvfmfunct6,
    ``LeanRV64D.fvffunct6, ``LeanRV64D.fvvmafunct6, ``LeanRV64D.fvvmfunct6, ``LeanRV64D.fvvfunct6,
    ``LeanRV64D.fwffunct6, ``LeanRV64D.fwvfmafunct6, ``LeanRV64D.fwvffunct6, ``LeanRV64D.fwvfunct6,
    ``LeanRV64D.fwvvmafunct6, ``LeanRV64D.fwvvfunct6, ``LeanRV64D.indexed_mop, ``LeanRV64D.iop,
    ``LeanRV64D.hlvop, ``LeanRV64D.mmfunct6, ``LeanRV64D.mul_op, ``LeanRV64D.mvvmafunct6,
    ``LeanRV64D.mvvfunct6, ``LeanRV64D.mvxmafunct6, ``LeanRV64D.mvxfunct6, ``LeanRV64D.nisfunct6,
    ``LeanRV64D.nifunct6, ``LeanRV64D.ntl_type, ``LeanRV64D.nvsfunct6, ``LeanRV64D.nvfunct6,
    ``LeanRV64D.nxsfunct6, ``LeanRV64D.nxfunct6, ``LeanRV64D.rfvvfunct6, ``LeanRV64D.rfwvvfunct6,
    ``LeanRV64D.rivvfunct6, ``LeanRV64D.rmvvfunct6, ``LeanRV64D.rop, ``LeanRV64D.ropw, ``LeanRV64D.sop,
    ``LeanRV64D.sopw, ``LeanRV64D.uop, ``LeanRV64D.zvabd_vabd_func6, ``LeanRV64D.zvk_vaesdf_funct6,
    ``LeanRV64D.zvk_vaesdm_funct6, ``LeanRV64D.zvk_vaesef_funct6, ``LeanRV64D.zvk_vaesem_funct6,
    ``LeanRV64D.vextfunct6, ``LeanRV64D.vfnunary0, ``LeanRV64D.vfunary0, ``LeanRV64D.vfunary1,
    ``LeanRV64D.vfwunary0, ``LeanRV64D.vicmpfunct6, ``LeanRV64D.vimcfunct6, ``LeanRV64D.vimsfunct6,
    ``LeanRV64D.vimfunct6, ``LeanRV64D.visgfunct6, ``LeanRV64D.vifunct6, ``LeanRV64D.vlewidth,
    ``LeanRV64D.vmlsop, ``LeanRV64D.zvk_vsha2_funct6, ``LeanRV64D.zvk_vsm4r_funct6, ``LeanRV64D.vvcmpfunct6,
    ``LeanRV64D.vvmcfunct6, ``LeanRV64D.vvmsfunct6, ``LeanRV64D.vvmfunct6, ``LeanRV64D.vvfunct6,
    ``LeanRV64D.zvabd_vwabda_func6, ``LeanRV64D.vxcmpfunct6, ``LeanRV64D.vxmcfunct6, ``LeanRV64D.vxmsfunct6,
    ``LeanRV64D.vxmfunct6, ``LeanRV64D.vxsgfunct6, ``LeanRV64D.vxfunct6, ``LeanRV64D.wmvvfunct6,
    ``LeanRV64D.wmvxfunct6, ``LeanRV64D.wvfunct6, ``LeanRV64D.wvvfunct6, ``LeanRV64D.wvxfunct6,
    ``LeanRV64D.wxfunct6, ``LeanRV64D.extop_zbb, ``LeanRV64D.brop_zbb, ``LeanRV64D.bropw_zbb,
    ``LeanRV64D.brop_zbkb, ``LeanRV64D.biop_zbs, ``LeanRV64D.brop_zbs, ``LeanRV64D.zicondop,
    ``LeanRV64D.zilx_mode, ``LeanRV64D.f_un_rm_ff_op_S, ``LeanRV64D.wrsop, ``LeanRV64D.instruction_chunk0,
    ``LeanRV64D.instruction_chunk1, ``LeanRV64D.instruction, ``LeanRV64D.WaitReason, ``LeanRV64D.Privilege,
    ``LeanRV64D.instr_info, ``LeanRV64D.HartState] do
    let suffix := String.join ((typeName.getString!.splitOn "_").map String.capitalize)
    deriveDecidableEqNamed typeName (Name.mkSimple ("instDecidableEq" ++ suffix))

instance instructionBEq : BEq instruction := ⟨fun left right => decide (left = right)⟩
instance : ReflBEq instruction where
  rfl := by intro value; exact decide_eq_true rfl
instance : LawfulBEq instruction where
  eq_of_beq := by intro left right same; exact of_decide_eq_true same

deriving instance ReflBEq, LawfulBEq for WaitReason, Privilege, misaligned_exception,
  MemoryRegionType, AtomicSupport, Reservability, PMAMisalignedExceptions, PMA, PMA_Region,
  physaddr, TranslationStage, TLB_Entry, tdata, event_csr,
  Trig_Action, Hit, Compare_Selection, Trig_Match, TExtra, TDisabled, MControl6, ICount,
  ITrigger, ETrigger, Trigger

instance instrInfoBEq : BEq instr_info := ⟨fun left right => decide (left = right)⟩
instance : ReflBEq instr_info where
  rfl := by intro value; exact decide_eq_true rfl
instance : LawfulBEq instr_info where
  eq_of_beq := by intro left right same; exact of_decide_eq_true same

instance hartStateBEq : BEq HartState := ⟨fun left right => decide (left = right)⟩
instance : ReflBEq HartState where
  rfl := by intro value; exact decide_eq_true rfl
instance : LawfulBEq HartState where
  eq_of_beq := by intro left right same; exact of_decide_eq_true same

namespace SailRegisterFile

abbrev Map := Std.ExtDHashMap Register RegisterType

private instance valueBEq (reg : Register) : BEq (RegisterType reg) := by
  cases reg <;> infer_instance

private instance valueLawfulBEq (reg : Register) : LawfulBEq (RegisterType reg) := by
  cases reg <;> infer_instance

/-- Compare every stored register using Std's extensional finite-map comparison. -/
def equivalent (left right : Map) : Bool := left == right

theorem equivalent_iff (left right : Map) : equivalent left right = true ↔ left = right := by
  exact beq_iff_eq

end SailRegisterFile

end SP1Clean.Model.Core
