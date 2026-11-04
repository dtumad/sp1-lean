import SP1Clean.Native.Operations.WritePermission
import SP1CleanTest.Core.ComponentExport
import ToClean.Air.EnsembleCheck
import ToClean.Gadgets.LookupProjection

/-! # Closed export of native byte-write permissions

The production request circuit and fixed interval provider use Clean's built-in row programs,
scheduler and Rust emitter. Three public address requests drive ordinary demand rows; the production
circuit selects and authenticates each interval internally, with no private interval or address
inputs. The fourth row is disabled padding, retaining both zero-multiplicity channel occurrences.
The policy is native ROM exclusion, not SP1's runtime mprotect state machine.
-/

namespace SP1CleanTest.Core.WritePermissionExport

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core
open ComponentExport (Fp)

/-- Three byte addresses, with every native address limb retained. -/
abbrev Requests := ProvableVector (fields 3) 3

/-- Unsorted, repeated ROM entries exercise adjacent bytes, gaps and high address limbs. -/
def image : ProgramImage :=
  ⟨[(131072, 0x73), (65536, 0x00710093), (65536, 0x00710093),
    (0x200040004, 0x003100b3)], 65536, []⟩

/-- An empty ROM permits every native byte address. -/
def emptyImage : ProgramImage := ⟨[], 0, []⟩

/-- Keep the production permission request and all its assertions. -/
def requestComponent (rom : ProgramImage) : Component Fp :=
  WritePermissionProvider.component rom

/-- Public requests each consume one permission, including repeated addresses. -/
def verifier : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := do
    Verifier.pull WritePermissionProvider.channel requests[0]
    Verifier.pull WritePermissionProvider.channel requests[1]
    Verifier.pull WritePermissionProvider.channel requests[2]

/-- Both permission protocols are closed by production components. -/
def ensemble (rom : ProgramImage) : Ensemble Fp Requests where
  tables := [requestComponent rom, WritePermissionProvider.membershipComponent rom]
  unique_names := by
    simp [requestComponent, WritePermissionProvider.component, WritePermissionProvider.circuit,
      Circuit.Guarded.circuit, WritePermissionProvider.activeCircuit,
      WritePermissionProvider.membershipComponent, StaticTable.component, StaticTable.provider,
      ProgramImage.writePermissionTable, StaticTable.ofRows]
  channels := [WritePermissionProvider.channel.toRaw, rom.writePermissionTable.channel.toRaw]
  verifier := verifier
  unique_channel_names := by
    simp [WritePermissionProvider.channel, Channel.toRaw, StaticTable.channel,
      ProgramImage.writePermissionTable, StaticTable.ofRows]
  tables_channels := by
    intro component member channel used
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · change channel ∈ [rom.writePermissionTable.channel.toRaw,
        WritePermissionProvider.channel.toRaw] at used
      simp only [List.mem_cons, List.not_mem_nil, or_false] at used ⊢
      exact used.elim Or.inr Or.inl
    · change channel ∈ [rom.writePermissionTable.channel.toRaw] at used
      exact List.mem_cons_of_mem _ used
  verifier_channels := by
    intro channel member
    simp [Verifier.Program.channels, Verifier.Program.channelsWithGuarantees,
      Verifier.Program.channelsWithRequirements, Verifier.Program.operations, verifier,
      circuit_norm] at member
    simp [member]

/-- Raw acceptance checks every local assertion and both complete channel ledgers. -/
def description (rom : ProgramImage) : EnsembleCheck (ensemble rom) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, requestComponent, WritePermissionProvider.component,
      WritePermissionProvider.membershipComponent, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]

/-- Generate from addresses alone with Clean's shared interpreter and scheduler. -/
def generate (rom : ProgramImage) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble rom)) :=
  WitnessGeneration.generate (ensemble rom) 8
    requests () |>.mapError toString

/-- Rust emission includes both production components and the fixture's input programs. -/
def rustExports : List (String × Except String String) :=
  [("write_permission.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble image)) 8),
   ("write_permission_empty.rs", Backends.Plonky3.Print.ensembleToRust
      (ComponentExport.fixture (ensemble emptyImage)) 8)]

/-- Boundary addresses, repeats, code bytes and noncanonical field limbs. -/
def cases : List (String × Requests Fp × Bool) :=
  ([0, 65535, 65540, 131071, 131076, 0x200040003, 0x200040008, 2 ^ 48 - 1].map
    fun address => (s!"writable-{address}", #v[Address.ofNat address, Address.ofNat address, Address.ofNat address], true)) ++
  ([65536, 65539, 131072, 131075, 0x200040004, 0x200040007].map
    fun address => (s!"code-{address}", #v[Address.ofNat address, Address.ofNat 65540, Address.ofNat 65540], false)) ++
  [("mixed-intervals", #v[Address.ofNat 65540, Address.ofNat 131076, Address.ofNat 65540], true),
   ("noncanonical-low", #v[#v[65536, 0, 0], Address.ofNat 65540, Address.ofNat 65540], false),
   ("noncanonical-high", #v[#v[0, 0, 65536], Address.ofNat 65540, Address.ofNat 65540], false)]

end SP1CleanTest.Core.WritePermissionExport
