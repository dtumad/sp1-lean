import SP1CleanTest.Alignment.Support.InstalledAssembly
import SP1CleanTest.Core.HintReadFixtures
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Model.Core.HostSnapshot

/-! # Complete active HINT_READ assembly fixture

The semantic host step supplies the target snapshot. Its three register locations and every
padded hint word have actual source/final Memory records and target checks. The sixteen-byte
case needs three RAM words, exercising inactive padding in all six boundary/check tables.
The twenty-four-byte case pads three nonfinal word consumers to four physical rows.
This finite export fixture does not assert general generation completeness.
-/

namespace SP1CleanTest.Alignment.HintReadAssembly

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness
open SP1CleanTest.Alignment.InstalledAssembly

private abbrev image := SP1CleanTest.Core.HintReadFixtures.image
private def program : Target.GuestProgram := image.toGuestProgram (by decide)
private def policy : HostPolicy :=
  ⟨⟨fun address => decide (131072 ≤ address ∧ address < 131076), 65536, 2 ^ 48⟩, SP1Prime⟩
private abbrev bytes := SP1CleanTest.Core.HintReadFixtures.bytes
private def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)
private def source (length : ℕ) : ExecutionSnapshot where
  sail := {
    registers := (((Target.configuredState 131072).regs.insert .x5 241).insert .x10 65536).insert
      .x11 (BitVec.ofNat 64 length)
    memory := image.initialMemory.writeBytes 65536
      (List.replicate (8 * HintQueue.wordCount (bytes length)) 255) }
  host := { io := { hints := [bytes length] } }
  clock := 9

/-- Public endpoints of one continuing HINT_READ call at clock nine. -/
def header : SP1PublicIO Fp where
  init_clk_0_16 := 9
  init_clk_16_24 := 0
  init_clk_24_32 := 0
  init_clk_32_48 := 0
  init_pc0 := 0
  init_pc1 := 2
  init_pc2 := 0
  final_clk_0_16 := 273
  final_clk_16_24 := 0
  final_clk_24_32 := 0
  final_clk_32_48 := 0
  final_pc0 := 4
  final_pc1 := 2
  final_pc2 := 0
  exit_code := 0
  is_execution_shard := 1
  committed_value_digest := Vector.replicate 32 0

private def instruction (length : ℕ) : HostCallChip.Inputs Fp :=
  HostCallChip.populate
    { state := ⟨0, 0, 9, #v[0, 2, 0]⟩
      op_a := 5, op_a_memory := ⟨word 241, ⟨0, 12⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨word 65536, ⟨0, 11⟩⟩
      op_c := 11, op_c_memory := ⟨word length, ⟨0, 10⟩⟩
      next_pc := #v[4, 2, 0], is_halt := 0, op_a_value := word 241
      syscall_id_bytes := U16toU8OperationSafe.populate (word 241)
      is_enter_unconstrained := IsZeroOperation.populate (238 : Fp)
      is_hint_len := IsZeroOperation.populate (1 : Fp)
      is_halt_zero := IsZeroOperation.populate (241 : Fp)
      is_commit := IsZeroOperation.populate (225 : Fp)
      is_commit_deferred := IsZeroOperation.populate (215 : Fp)
      digest_index_bits := Vector.replicate 8 0, digest_word := 0
      op_b_cmp := ⟨1⟩, op_c_cmp := ⟨1⟩, is_real := 1 }
    0 0

private def memoryRecord (address clock : ℕ) (value : BitVec 64) : Channels.MemoryMsg Fp :=
  let key := Address.ofNat (p := SP1Prime) address
  ⟨0, clock, key[0], key[1], key[2], Target.bitVecToWord value⟩

/-- Construct the complete source, target and physical consumers from a semantic host step. -/
def prepare (length : ℕ) : Except String (Context × List Seed) := do
  let incoming := source length
  let some (outgoing, _) := incoming.hostStep? policy program
    | throw "finite semantic HINT_READ step failed"
  let some executed := incoming.host.run policy incoming.sail.readContext
    | throw "finite host dispatch failed"
  let store := HintQueue.ofList incoming.host.io.hints
  let handler := HostHintReadChip.populate (p := SP1Prime) store.1 store.2 0 9 executed
  let context : Context := {
    image, source := incoming, target := outgoing.sail.memorySnapshot
    finalHints := handler.next, finalHost := outgoing.host }
  let registers := [(5, 13), (10, 12), (11, 11)]
  let registerSeeds := (registers.foldl (fun (acc : ℕ × List Seed) (address, clock) =>
    let index := BitVec.ofNat 5 address
    let record := memoryRecord address clock (context.target.read (.reg index))
    let initial := OrderedSnapshotProvider.populate
      (SnapshotRegisterProvider.populate incoming.sail.memorySnapshot index) acc.1 address
    let final := OrderedMemoryProvider.populate record acc.1 address
    (address + 1, acc.2 ++ [⟨0, (toElements initial).toList⟩, ⟨3, (toElements final).toList⟩,
      ⟨90, (toElements (M := FinalRegisterCheck.RowInput) ((⟨record, 0⟩, 1) : FinalRegisterCheck.RowInput Fp)).toList⟩])) (0, [])).2
  let count := HintQueue.wordCount (bytes length)
  let (lastKey, ramSeeds) := (List.range count).foldl
    (fun (acc : ℕ × List Seed) index =>
      let address := 65536 + 8 * index
      let prior := memoryRecord address 0 (incoming.sail.memory.readWord address)
      let record := memoryRecord address 10 (outgoing.sail.memory.readWord address)
      let initial := OrderedSnapshotProvider.populate (word address) acc.1 address
      let final := OrderedMemoryProvider.populate record acc.1 address
      let ram := HostRamAccessChip.populate prior 0 9 0 record.value
      let last := decide (index + 1 = count)
      let transfer := HintReadWordChip.populate last ram (Address.ofNat store.2) (Address.ofNat index)
      (address + 1, acc.2 ++ [⟨1, (toElements initial).toList⟩, ⟨4, (toElements final).toList⟩,
        ⟨91, (toElements (M := FinalRamCheck.RowInput) ((⟨record, 1⟩, 1) : FinalRamCheck.RowInput Fp)).toList⟩,
        ⟨if last then 85 else 84, (toElements transfer).toList⟩])) (12, [])
  let terminal := toElements (OrderedBoundaryEnd.populate (word lastKey)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime))) |>.toList
  let remaining := (emptyConsumers context).filter fun seed =>
    seed.table == 57 || seed.table == 88 || seed.table == 89
  return (context, registerSeeds ++ ramSeeds ++ remaining ++
    [⟨2, terminal⟩, ⟨5, terminal⟩, ⟨58, (toElements (instruction length)).toList⟩,
     ⟨63, (toElements handler).toList⟩])

end SP1CleanTest.Alignment.HintReadAssembly
