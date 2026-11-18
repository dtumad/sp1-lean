module

public import SP1Clean.Semantics.Sail.SailWrap

/-! # Reducing the official Sail decoder `ext_decode`

`try_step` decodes via `ext_decode = encdec_backwards` (`LeanRV64D/InstsEnd.lean`), a `noncomputable`
~395-arm nested cascade. The symbolic family lemmas (`Proofs/Sail/InstructionDecode/Families.lean`)
walk it with the rewrites below, and `instructionDecode_agrees` turns them into the
`ConfiguredDecode` fact for every word the executable decoder accepts. A concrete word's decode
therefore follows from `instructionDecode_agrees _ _ rfl`, which evaluates the small executable
decoder instead of the cascade.

**The unstick rewrites.** Every arm guard except a handful is a pure bit test on the word, so `whnf`
drives the pure prefix in one step. It parks exactly at the guards that consult machine state, each
whnf-opaque for a stated reason:

* `currentlyEnabled` is **well-founded-recursive** (its extension graph is not structural on the
  flat `extension` enum), so even its config-constant arms never whnf-reduce — `cePause_apply`
  unsticks the PAUSE-arm head, whose value is the config constant `hartSupports Ext_Zihintpause`.
* the Zicfilp/forward-CFI cluster reads `cur_privilege` and `mseccfg.MLPE` — a genuine state read;
  `ceZicfilp_bind_apply` resolves it to `false` from the machine-mode and MLPE-off `SailConfigured`
  residues (the same fields `update_elp_state_of_isInitialized` consumes on the execute side).
* the M-extension arms read `misa.M`; `ceM_apply` and `ceZmmul_apply` resolve it under the
  `SailConfigured.misa_m` pin, and `run_bind_step` takes the matching arm.

`decode_ECALL` is the one concrete walk kept here: the agreement proof itself uses it, since the
executable decoder rejects `ECALL`. Its hypotheses are the raw register facts (`isInitialized`, the
machine-mode `cur_privilege`, the `mseccfg` bit-10 pin) rather than `SailConfigured`, which lives
above this file. -/

@[expose] public section

open LeanRV64D
namespace SP1Clean.SailDecode

open Sail Sail.ArchSem LeanRV64D LeanRV64D.Functions

set_option linter.unusedSimpArgs false

/-- Keep the decoder's large continuation folded while exposing a bind rewrite. -/
theorem free_bind_eq_bind {α β : Type} (m : SailM α) (f : α → SailM β) :
    FreeM.bind m f = m >>= f := rfl

/-! ## The unstick rewrites — one per whnf-opaque guard head on the base-family walk -/

/-- The PAUSE-arm guard head: `currentlyEnabled Ext_Zihintpause` is the config constant
`hartSupports Ext_Zihintpause` (no state read), but `currentlyEnabled` is well-founded-recursive so
it never whnf-reduces; this equation lets the walk continue. Stated applied to `s` — the form the
whnf'd goal exposes. -/
theorem cePause_apply :
    currentlyEnabled extension.Ext_Zihintpause = (pure true : SailM Bool) := by
  simp [currentlyEnabled.eq_def, hartSupports.eq_def]

/-- The Zicfilp/forward-CFI cluster head: under machine mode with `mseccfg.MLPE = 0` (bit 10, the
`SailConfigured.mseccfg_disabled` residue), `currentlyEnabled Ext_Zicfilp` resolves to `false` —
the LPAD arm is dead and the walk continues into the base-ISA arms. Mirrors the execute-side
`update_elp_state_of_isInitialized` (`Semantics/Sail/SailMemory.lean`). -/
theorem ceZicfilp_bind_apply {α : Type} (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (k : Bool → SailM α) :
    runSail (currentlyEnabled extension.Ext_Zicfilp >>= k) s = runSail (k false) s := by
  have hpriv' : s.regs.get Register.cur_privilege (hs _) = Privilege.Machine := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpriv
  have hmlpe : Sail.BitVec.extractLsb (s.regs.get Register.mseccfg (hs _)) 10 10 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    rw [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat]
    have h2 := congrArg BitVec.toNat hseccfg
    simp only [BitVec.toNat_ofNat] at h2 ⊢
    omega
  show (runSail ((currentlyEnabled extension.Ext_Zicfilp >>= k) : SailM α)) s = (runSail (k false)) s
  simp only [andM, orM, toBool, currentlyEnabled.eq_def, get_xLPE, hartSupports.eq_def, _get_Seccfg_MLPE,
    bool_bit_backwards, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hpriv', hmlpe,
    Bool.true_and, Bool.and_false, Bool.false_and, ite_false]
  rfl

/-! ## The concrete ECALL walk -/

/-- The fixed RV64 `ECALL` word.  This decoder fact is used only negatively by the ordinary-shard
bridge: a successful supported Program-row projection cannot be this constructor. -/
theorem decode_ECALL (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (runSail (ext_decode 0x00000073#32)) s = .ok (instruction.ECALL ()) s := by
  conv_lhs => arg 1; whnf
  rw [cePause_apply]
  conv_lhs => arg 1; whnf
  rw [free_bind_eq_bind, bind_assoc, ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => arg 1; whnf
  rfl

/-! ## The M-extension unsticks

The MUL/DIV arms guard on `currentlyEnabled Ext_M` (directly, or through `Ext_Zmmul`, whose
`hartSupports` is `false` in this configuration so it reduces to the same `misa.M` test). The bit is
pinned by `SailConfigured.misa_m`. The walk parks at the matching arm's own guard (the reads sit
inside the taken arm), so the take goes through `run_bind_step` — a generic peel of the
`EStateM`-bind match at a state-preserving `.ok`. -/

/-- Execute a known state-preserving prefix, leaving its continuation folded. -/
theorem run_bind_step {α β : Type} (m : SailM α) (v : α) (k : α → SailM β)
    (s : SailState) (h : runSail m s = .ok v s) :
    runSail (m >>= k) s = runSail (k v) s := by
  rw [runSail_bind, h]

/-- `currentlyEnabled Ext_M` is `true` under the `misa.M` pin (`hartSupports Ext_M` is a config
`true`; the guard is exactly the `misa.M` bit). -/
theorem ceM_apply (s : SailState) (hs : s.isInitialized)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    runSail (currentlyEnabled extension.Ext_M) s = EStateM.Result.ok true s := by
  show (runSail (currentlyEnabled extension.Ext_M)) s = .ok true s
  simp only [andM, orM, toBool, currentlyEnabled.eq_def, hartSupports.eq_def, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hmisa, Bool.true_and, beq_self_eq_true]
  rfl

/-- `currentlyEnabled Ext_Zmmul` reduces to `currentlyEnabled Ext_M` (`hartSupports Ext_Zmmul` is a
config `false`), hence `true` under the same pin. -/
theorem ceZmmul_apply (s : SailState) (hs : s.isInitialized)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    runSail (currentlyEnabled extension.Ext_Zmmul) s = EStateM.Result.ok true s := by
  show (runSail (currentlyEnabled extension.Ext_Zmmul)) s = .ok true s
  simp only [andM, orM, toBool, currentlyEnabled.eq_def, hartSupports.eq_def, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hmisa, Bool.true_and, Bool.false_or,
    beq_self_eq_true]
  rfl

end SP1Clean.SailDecode
