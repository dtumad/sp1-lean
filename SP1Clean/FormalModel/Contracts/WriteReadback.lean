import SP1Clean.FormalModel.Contracts.WriteProbe

/-! # Private receipt for unchanged-word WRITE versions and finalized suffixes

The same receipt retains the Memory bus's 24-bit clock limbs before conversion to the
16-bit limbs of the probe. It records the held word over a closed interval.
-/

namespace SP1Clean.WriteProbe

/-- A read-back edge in the original Memory ledger. Clock limbs are the original 24-bit bus cells. -/
structure Readback (F : Type) where
  /-- Canonical three-limb Memory address. -/
  key : fields 3 F
  /-- Upper 24 bits of the first included timestamp. -/
  previousHigh : F
  /-- Lower 24 bits of the first included timestamp. -/
  previousLow : F
  /-- Upper 24 bits of the last included timestamp. -/
  currentHigh : F
  /-- Lower 24 bits of the last included timestamp. -/
  currentLow : F
  /-- Word preserved throughout the inclusive range. -/
  value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Readback

/-- Mandatory unit receipts originate in the read-back rows. A separate consumer assigns query counts. -/
def readbackChannel {p : ℕ} : Channel (ZMod p) Readback where
  name := "sp1.native.write_readback"
  Guarantees _ _ := True

end SP1Clean.WriteProbe
