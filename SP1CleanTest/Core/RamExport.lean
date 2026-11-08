import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.SnapshotRamProvider
import SP1Clean.Native.Operations.FinalRamValue
import ToClean.Air.EnsembleCheck
import ToClean.Air.TableBuild

/-! # Built-in Rust export of RAM rows and fixed interval membership

Clean owns witness execution, fixed rows, scheduling and lowering. The closed membership fixture
checks the production interval provider. Component fixtures retain their external Byte and Memory
interactions; Rust checks those separately. They do not establish full-ensemble generation.
-/

namespace SP1CleanTest.Core.RamExport

open Air.Flat Circuit SP1Clean SP1Clean.Model.Core

abbrev Fp := ZMod SP1Prime
abbrev Requests := ProvableVector MemoryIntervalRow 2

/-- Unsorted entries include first-write precedence, a sparse gap and the final native byte. -/
def memory : ByteMemory :=
  ⟨[(131072, 18), (65536, 17), (65536, 99), (65543, 171),
    (131071, 254), (2 ^ 48 - 1, 255)]⟩

def snapshot : MemorySnapshot := ⟨Vector.replicate 32 0, memory⟩

def table (name : String) : StaticTable Fp MemoryIntervalRow :=
  InitialMemoryLookup.membership memory (2 ^ 48) name

def verifier (name : String) : Verifier.Program Fp Requests where
  Spec _ _ := True
  soundness := by intros; trivial
  main requests := do
    Verifier.pull (table name).channel ⟨requests[0], 1⟩
    Verifier.pull (table name).channel ⟨requests[1], 1⟩

def ensemble (name : String) : Ensemble Fp Requests where
  tables := [(table name).component (InitialMemoryLookup.membership_height_lt_uint64 memory name)]
  unique_names := by simp
  channels := [(table name).channel.toRaw]
  verifier := verifier name
  unique_channel_names := by simp
  tables_channels := by
    intro component member
    obtain rfl := List.mem_singleton.mp member
    change [(table name).channel.toRaw] ⊆ _
    simp
  verifier_channels := by
    intro channel member
    simp [Verifier.Program.channels, Verifier.Program.channelsWithGuarantees,
      Verifier.Program.channelsWithRequirements, Verifier.Program.operations, verifier,
      circuit_norm] at member
    simpa using member


def description (name : String) : Air.Flat.EnsembleCheck (ensemble name) where
  lookups := []
  lookups_unique := by simp
  lookups_complete := by
    simp [ensemble, Component.lookups_eq, Component.rowOperations,
      StaticTable.component, StaticTable.provider, circuit_norm]

def generate (name : String) (requests : Requests Fp) :
    Except String (EnsembleWitness (ensemble name)) :=
  WitnessGeneration.generate (ensemble name) 8 requests () |>.mapError toString

/-- The complete normalized interval inventory, then a repeated request and independent forgeries. -/
def cases : List (String × Requests Fp × Bool) :=
  let rows := (memory.intervals (2 ^ 48)).map (MemoryInterval.encode (p := SP1Prime))
  let first : MemoryIntervalRow Fp := (⟨65536, 65537, 17⟩ : MemoryInterval).encode
  rows.zipIdx |>.map (fun (row, index) => (s!"interval-{index}", #v[row, first], true)) |>.append
    [("repeated", #v[first, first], true),
     ("forged-byte", #v[(⟨65536, 65537, 99⟩ : MemoryInterval).encode, first], false),
     ("forged-lower", #v[(⟨65535, 65537, 17⟩ : MemoryInterval).encode, first], false),
     ("forged-upper", #v[(⟨65536, 65538, 17⟩ : MemoryInterval).encode, first], false)]

def exportRow {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (circuit : GeneralFormalCircuit Fp Input Output) : Except String String :=
  ComponentExport.exportRust circuit

def rustExports : List (String × Except String String) :=
  [("ram_byte.rs", exportRow (InitialMemoryLookup.circuit memory (2 ^ 48) (by norm_num))),
   ("ram_word.rs", exportRow (InitialMemoryRead.circuit memory)),
   ("ram_source.rs", exportRow (SnapshotRamProvider.circuit snapshot)),
   ("ram_target.rs", exportRow (FinalRamValue.circuit snapshot)),
   ("ram_source_membership.rs", Backends.Plonky3.Print.ensembleToRust
     (ComponentExport.fixture (ensemble "sp1.native.initial_memory")) 8),
   ("ram_target_membership.rs", Backends.Plonky3.Print.ensembleToRust
     (ComponentExport.fixture (ensemble "sp1.native.target_memory")) 8)]

/-- Public test inputs cover carries, sparse gaps, native bounds and malformed field limbs. -/
def rowCases : List (String × Component Fp × List (List Fp)) :=
  let addresses := [0, 31, 32, 65529, 65536, 65537, 65543, 131064, 131065, 131072,
    2 ^ 48 - 8, 2 ^ 48 - 7, 2 ^ 48 - 1, 2 ^ 48]
  let words := addresses.map fun address =>
    (Soundness.Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)).toList
  let inputs := words ++ [[65536, 0, 0, 0]]
  let records := addresses.map fun address =>
    let addr := Soundness.Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
    let value := Soundness.Target.bitVecToWord (p := SP1Prime) (memory.readWord address)
    [(3 : Fp), 17, addr[0], addr[1], addr[2]] ++ value.toList
  [("byte", ComponentExport.component (InitialMemoryLookup.circuit memory (2 ^ 48) (by norm_num)), inputs),
   ("word", ComponentExport.component (InitialMemoryRead.circuit memory), inputs),
   ("source", ComponentExport.component (SnapshotRamProvider.circuit snapshot), inputs),
   ("target", ComponentExport.component (FinalRamValue.circuit snapshot),
     records ++ [[3, 17, 0, 1, 0, 99, 0, 0, 0], [3, 17, 65536, 0, 0, 17, 0, 0, 0]])]

theorem cases_correct :
    ["sp1.native.initial_memory", "sp1.native.target_memory"].all (fun name =>
      cases.all fun (_, requests, expected) =>
        (match generate name requests with
        | .ok witness => (description name).checkWitness witness
        | .error _ => false) == expected) = true := by native_decide

theorem exports_succeed : rustExports.all (fun entry => entry.2.isOk) = true := by native_decide

end SP1CleanTest.Core.RamExport
