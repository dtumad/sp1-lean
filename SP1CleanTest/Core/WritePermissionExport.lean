import SP1Clean.Native.Operations.WritePermission
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.EnsembleCheck
import ToClean.Gadgets.LookupProjection

/-! # Closed export of native byte-write permissions

The production request circuit and fixed interval provider use Clean's built-in row programs,
scheduler and Rust emitter. Two public address requests drive ordinary demand rows; the production
circuit selects and authenticates each interval internally, with no private interval or address
inputs. General table padding remains a separate installed-assembly obligation.
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

/-- Route public requests directly; preallocate the complete fixed inventory for count updates. -/
def config (rom : ProgramImage) : WitnessGeneration.Config Fp where
  components := [((requestComponent rom).circuit.name, {
    mode := .demand {
      channel := WritePermissionProvider.channel.toRaw
      direction := .pull
      aggregation := .perOccurrence
      input := ⟨[.message 0, .message 1, .message 2]⟩
    }
    padding := { input := Array.replicate 3 0 }
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
  WitnessGeneration.generate (ComponentExport.fixture (ensemble rom)) (config rom)
    requests () |>.mapError toString

/-- Rust emission includes both production components and the fixture's input programs. -/
def rustExports : List (String × Except String String) :=
  [("write_permission.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble image)) (config image)),
   ("write_permission_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble emptyImage)) (config emptyImage))]

/-- Boundary addresses, repeats, code bytes and noncanonical field limbs. -/
def cases : List (String × Requests Fp × Bool) :=
  ([0, 65535, 65540, 131071, 131076, 0x200040003, 0x200040008, 2 ^ 48 - 1].map
    fun address => (s!"writable-{address}", #v[Address.ofNat address, Address.ofNat address], true)) ++
  ([65536, 65539, 131072, 131075, 0x200040004, 0x200040007].map
    fun address => (s!"code-{address}", #v[Address.ofNat address, Address.ofNat 65540], false)) ++
  [("mixed-intervals", #v[Address.ofNat 65540, Address.ofNat 131076], true),
   ("noncanonical-low", #v[#v[65536, 0, 0], Address.ofNat 65540], false),
   ("noncanonical-high", #v[#v[0, 0, 65536], Address.ofNat 65540], false)]

end SP1CleanTest.Core.WritePermissionExport
