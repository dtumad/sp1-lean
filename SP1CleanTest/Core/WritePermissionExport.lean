import SP1Clean.Native.Operations.WritePermission
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.EnsembleCheck
import ToClean.Gadgets.LookupProjection

/-! # Closed export of native byte-write permissions

The production request circuit and fixed interval provider use Clean's built-in row programs,
scheduler and Rust emitter. Two address requests supply the public boundary and private generation
input. A preallocated row program selects each interval using the existing witness IR; this finite
fixture does not provide an address-driven demand handler for a complete machine.
The policy is native ROM exclusion, not SP1's runtime mprotect state machine.
-/

namespace SP1CleanTest.Core.WritePermissionExport

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core
open ComponentExport (Fp)

/-- Two byte addresses, with every native address limb retained. -/
abbrev Requests := ProvableVector (fields 3) 2

/-- Unsorted, repeated ROM entries exercise adjacent bytes, gaps and high address limbs. -/
def image : ProgramImage :=
  ⟨[(131072, 0x73), (65536, 0x00710093), (65536, 0x00710093),
    (0x200040004, 0x003100b3)], 65536, []⟩

/-- An empty ROM permits every native byte address. -/
def emptyImage : ProgramImage := ⟨[], 0, []⟩

/-- Keep the production permission request and all its assertions. -/
def requestComponent (rom : ProgramImage) : Component Fp :=
  { circuit := WritePermissionProvider.circuit rom
    Assumptions := (WritePermissionProvider.circuit rom).Assumptions }

/-- Public requests each consume one permission, including repeated addresses. -/
def verifier : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := do
    Verifier.pull WritePermissionProvider.channel requests[0]
    Verifier.pull WritePermissionProvider.channel requests[1]

/-- Both permission protocols are closed by production components. -/
def ensemble (rom : ProgramImage) : Ensemble Fp Requests where
  tables := [requestComponent rom, WritePermissionProvider.membershipComponent rom]
  unique_names := by
    simp [requestComponent, WritePermissionProvider.circuit,
      WritePermissionProvider.membershipComponent, StaticTable.component, StaticTable.provider,
      ProgramImage.writePermissionTable, StaticTable.ofRows]
  channels := [WritePermissionProvider.channel.toRaw, rom.writePermissionTable.channel.toRaw]
  verifier := verifier

/-- Read one address limb from the fixture's two private address inputs. -/
def addressCell (column : UInt64) : Witgen.FExpr Fp :=
  .listGet (List.ofFn fun index : Fin 6 => .hintGet "input" 6 (.const 0) index)
    (.add (.mul .idx (.const 3)) (.const column))

/-- Native addresses fit in u64 without arithmetic wrap. Circuit assertions still enforce limbs. -/
def addressValue : Witgen.U64Expr Fp :=
  .add (.val (addressCell 0))
    (.add (.mul (.val (addressCell 1)) (.const 65536))
      (.mul (.val (addressCell 2)) (.const 4294967296)))

/-- Select an inclusive endpoint limb using only Clean's existing conditionals. A miss supplies
zero endpoints and remains subject to the circuit's membership and comparison checks. -/
def intervalCell : List MemoryInterval → Fin 6 → Witgen.FExpr Fp
  | [], _ => .const 0
  | interval :: rest, column =>
      .ite (if interval.lower = 0 then .lt addressValue (.const (UInt64.ofNat interval.upper)) else
        .and (.not (.lt addressValue (.const (UInt64.ofNat interval.lower))))
          (.lt addressValue (.const (UInt64.ofNat interval.upper))))
        (.const (toElements (WritePermissionInterval.encode (p := SP1Prime) interval))[column])
        (intervalCell rest column)

private theorem addressCell_valid (column : UInt64) :
    (addressCell column).validForRow .prover = true := by
  simp [addressCell, Witgen.FExpr.validForRow, Witgen.FExprList.validForRow, Witgen.U64Expr.validForRow,
    Witgen.RowProgram.Source.allowsHints]

private theorem intervalCell_valid (intervals : List MemoryInterval) (column : Fin 6) :
    (intervalCell intervals column).validForRow .prover = true := by
  induction intervals with
  | nil => rfl
  | cons interval rest ih =>
    simp only [intervalCell]
    split_ifs <;> simp [addressValue, Witgen.FExpr.validForRow, Witgen.BExpr.validForRow,
      Witgen.U64Expr.validForRow, addressCell_valid, ih]

/-- Preallocate two request rows and the complete fixed inventory. Clean owns count updates. -/
def config (rom : ProgramImage) : WitnessGeneration.Config Fp where
  components := [((requestComponent rom).circuit.name, {
    mode := .preallocated {
      rows := 2
      input := .ofFExprs #v[addressCell 0, addressCell 1, addressCell 2,
        intervalCell rom.writableIntervals 0, intervalCell rom.writableIntervals 1,
        intervalCell rom.writableIntervals 2, intervalCell rom.writableIntervals 3,
        intervalCell rom.writableIntervals 4, intervalCell rom.writableIntervals 5]
      input_valid := by
        simp [Witgen.RowProgram.Valid, Witgen.RowProgram.ofFExprs, Witgen.VExpr.validForRow,
          addressCell_valid, intervalCell_valid]
      handlers := []
    }
    padding := { input := Array.replicate 9 0 }
  }), ((WritePermissionProvider.membershipComponent (p := SP1Prime) rom).circuit.name, {
    mode := .preallocated {
      rows := UInt64.ofNat (rom.writePermissionTable (p := SP1Prime)).height
      input := .ofFExprs #v[.const 0]
      input_valid := by rfl
      handlers := [{ interaction := 0, column := 7 }]
    }
    padding := { input := Array.replicate 8 0 }
  })]
  fuel := 8

/-- Raw acceptance checks every local assertion and both complete channel ledgers. -/
def description (rom : ProgramImage) : EnsembleCheck (ensemble rom) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, requestComponent, WritePermissionProvider.membershipComponent,
      Component.lookups_eq, Component.rowOperations, StaticTable.component, StaticTable.provider,
      WritePermissionProvider.circuit, WritePermissionProvider.main,
      FormalAssertion.toSubcircuit_toFlat, AddressOrder.circuit, AddressOrder.main,
      Gadgets.ToBits.rangeCheck, Gadgets.ToBits.toBits, Gadgets.IsZeroField.circuit,
      Gadgets.Equality.main, circuit_norm]
  channels_unique := by
    simp [ensemble, WritePermissionProvider.channel, Channel.toRaw, StaticTable.channel,
      ProgramImage.writePermissionTable, StaticTable.ofRows]
  channels_complete := by
    intro component member interaction used
    rw [Component.interactions_eq] at used
    have declared := component.circuit.channels_subset component.rowInputVar component.rowOffset
      (List.mem_map_of_mem (f := AbstractInteraction.channel) used)
    simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change interaction.channel ∈ [rom.writePermissionTable.channel.toRaw,
        WritePermissionProvider.channel.toRaw] at declared
      simp only [ensemble, List.mem_cons, List.not_mem_nil, or_false] at declared ⊢
      exact declared.elim Or.inr Or.inl
    · change interaction.channel ∈ [rom.writePermissionTable.channel.toRaw] at declared
      exact List.mem_cons_of_mem _ declared
  verifier_channels_complete := by
    simp [ensemble, Ensemble.verifierOperations, verifier, Verifier.Program.circuitOperations, circuit_norm]

/-- Generate from addresses alone with Clean's shared interpreter and scheduler. -/
def generate (rom : ProgramImage) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble rom)) :=
  WitnessGeneration.generate (ComponentExport.fixture (ensemble rom) Requests) (config rom)
    requests requests |>.mapError toString

/-- Rust emission includes both production components and the fixture's input programs. -/
def rustExports : List (String × Except String String) :=
  [("write_permission.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble image) Requests) (config image)),
   ("write_permission_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble emptyImage) Requests) (config emptyImage))]

/-- Boundary addresses, repeats, code bytes and noncanonical field limbs. -/
def cases : List (String × Requests Fp × Bool) :=
  ([0, 65535, 65540, 131071, 131076, 0x200040003, 0x200040008, 2 ^ 48 - 1].map
    fun address => (s!"writable-{address}", #v[Address.ofNat address, Address.ofNat address], true)) ++
  ([65536, 65539, 131072, 131075, 0x200040004, 0x200040007].map
    fun address => (s!"code-{address}", #v[Address.ofNat address, Address.ofNat 65540], false)) ++
  [("noncanonical-low", #v[#v[65536, 0, 0], Address.ofNat 65540], false),
   ("noncanonical-high", #v[#v[0, 0, 65536], Address.ofNat 65540], false)]

end SP1CleanTest.Core.WritePermissionExport
