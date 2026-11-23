import SP1Clean.Math.Address
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Private read-only WRITE observation protocol

Three 16-bit limbs encode each canonical location and absolute time. The inclusive time range
contains exactly those incoming clocks where this version's four-limb value is live.
The two structural channels acquire their meaning from physical ledger balance.
-/

namespace SP1Clean.WriteProbe

/-- A version supplied by the physical history for one location. -/
structure Version (F : Type) where
  /-- Canonical SP1 Memory bus address. -/
  key : fields 3 F
  /-- First admitted incoming clock. -/
  lower : fields 3 F
  /-- Last admitted incoming clock. -/
  upper : fields 3 F
  /-- Held four-limb word. -/
  value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Version

/-- The host-facing receipt for one non-mutating probe. -/
structure Read (F : Type) where
  /-- x12 or an aligned guest RAM byte address. -/
  key : fields 3 F
  /-- Complete incoming CPU clock. -/
  clock : fields 3 F
  /-- Complete returned word. -/
  value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Read

/-- Active observer columns. The key division witness is computed from the selected key. -/
structure Inputs (F : Type) where
  /-- Actual interval occurrence requested on the private version bus. -/
  version : Version F
  /-- Incoming clock shared with the calling host row. -/
  clock : fields 3 F
  /-- Per-limb division witnesses for the aligned key check. -/
  quotients : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The interval and the emitted receipt share their address and value columns. -/
def Inputs.read {F : Type} (input : Inputs F) : Read F :=
  ⟨input.version.key, input.clock, input.version.value⟩

/-- A released WRITE probes x12 or an aligned RAM word in the guest window. -/
def ValidKey (key : ℕ) : Prop :=
  key = 12 ∨ (2 ^ 16 ≤ key ∧ key < 2 ^ 48 ∧ key % 8 = 0)

/-- The row checks all packed values and compares the canonical clock in integer order. -/
def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  Address.Bounded input.version.key ∧ ValidKey (Address.toNat input.version.key) ∧
  Word.isU64 input.version.value ∧ Address.Bounded input.version.lower ∧ Address.Bounded input.clock ∧
  Address.Bounded input.version.upper ∧ Address.toNat input.version.lower ≤ Address.toNat input.clock ∧
  Address.toNat input.clock ≤ Address.toNat input.version.upper

/-- Supplied by authenticated physical Memory versions and consumed by probe rows. -/
def versionChannel {p : ℕ} : Channel (ZMod p) Version where
  name := "sp1.native.write_version"
  Guarantees _ _ := True

/-- Supplied by probe rows and consumed by the handler's x12 and packet-word requests. -/
def readChannel {p : ℕ} : Channel (ZMod p) Read where
  name := "sp1.native.write_probe"
  Guarantees _ _ := True

end SP1Clean.WriteProbe
