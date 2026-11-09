import LeanRV64D.Defs

/-! # Generated RV64D floating-point widths

The D extension specifies 64-bit floating-point registers. Sail's previous Lean printer emitted
`if true then 8 else 4 * 8`, silently reducing their width to 8. Check the generated declarations
against the architectural width directly; a comparison between two outputs of the same compiler
would also accept that mistranslation.
-/

namespace SP1CleanTest.Alignment.Audit.SailWidths

/-- Check the register family itself, without an implicit resizing coercion. -/
theorem floatingRegisterType : LeanRV64D.RegisterType .f0 = BitVec 64 := rfl

end SP1CleanTest.Alignment.Audit.SailWidths
