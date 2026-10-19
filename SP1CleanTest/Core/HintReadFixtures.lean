import SP1CleanTest.Core.HintSourceExport
import SP1CleanTest.Core.HostChecks
import SP1Clean.Proofs.Chips.HintReadWordChip.Populate
import SP1Clean.Proofs.Chips.HintReadWordChip.Ledger
import SP1Clean.Native.Operations.HintQueueWordSource
import SP1Clean.Native.Operations.WritePermission
import SP1CleanTest.Core.StaticMembership

/-! # Shared executable fixtures for hint transfers

These helpers run the actual word, source, and permission circuits and compare their complete
non-Byte ledgers. Semantic Memory boundary fixtures are independent of the consumer row values.
The handler battery replaces the fixture cursor endpoints with the real handler's interactions.
-/

namespace SP1CleanTest.Core.HintReadFixtures

open Circuit Air.Flat SP1Clean Model.Core HintQueue HostChecks

/-- Field used by the native SP1 circuits. -/
abbrev Fp := ZMod SP1Prime
/-- Final-word selector paired with the word-transfer constructor input. -/
abbrev Row := Bool × HintReadWordChip.Inputs Fp

/-- Single-ECALL program image used to authenticate the fixture's write permissions. -/
def image : ProgramImage := ⟨[(131072, 0x00000073)], 131072, []⟩

/-- Deterministic byte payload with distinct values across adjacent word boundaries. -/
def bytes (length : ℕ) : Bytes := (List.range length).map fun i => BitVec.ofNat 8 (19 * i + 3)

/-- Initial RAM contents, chosen to expose missing writes and incorrect zero padding. -/
def oldWord : Word Fp := Soundness.Target.bitVecToWord (BitVec.allOnes 64)

/-- Construct the indexed hint word and its actual RAM update at the destination address. -/
def row (address : ℕ) (actual : Bytes) (index : ℕ) : Row :=
  let key := Address.ofNat (p := SP1Prime) (address + 8 * index)
  let word := WordRecord.encode (p := SP1Prime) 1 actual index
  let ram := HostRamAccessChip.populate ⟨0, 0, key[0], key[1], key[2], oldWord⟩ 0 1 0 word.value
  let last := decide (index + 1 = wordCount actual)
  (last, HintReadWordChip.populate last ram word.pointer word.index)

/-- All word transfers required by the payload, including its partial final word. -/
def rows (address : ℕ) (actual : Bytes) : List Row :=
  (List.range (wordCount actual)).map (row address actual)

/-- Execute one word transfer, optionally corrupting a generated witness cell. -/
def checked (row : Row) (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HintReadWordChip.main row.1 (varFromOffset HintReadWordChip.Inputs 0))
    (toElements row.2).toList corrupt

/-- Observe the requested word against the verifier-fixed payload inventory. -/
def source (actual : Bytes) (record : WordRecord Fp) : Bool × Ledger :=
  HintSourceExport.observe (HintSourceExport.words [actual]) record

/-- Check a writable byte address and include its physical fixed-membership provider ledger. -/
def permission (image : ProgramImage) (address : ℕ) : Bool × Ledger :=
  match WritePermissionProvider.populate? (p := SP1Prime) image address with
  | none => (false, [])
  | some input =>
    let request := evaluateProgram
      ((WritePermissionProvider.circuit image).main (varFromOffset WritePermissionProvider.RowInput 0))
      (toElements input).toList
    let membership := StaticMembership.providerLedger image.writePermissionTable request.2
      (WritePermissionProvider.membership_height_lt_uint64 image)
    (request.1, request.2 ++ membership)

/-- Require integer-bounded field balance for every non-Byte channel and message. -/
def balanced (ledger : Ledger) : Bool :=
  let selected := ledger.filter (fun item => item.1 != "SP1Byte")
  selected.length < SP1Prime && selected.all fun key =>
    ((selected.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

/-- Independent cursor and Memory endpoints from the semantic byte write, with padded tail. -/
def boundaries (address : ℕ) (actual : Bytes) : Ledger :=
  let count := wordCount actual
  let memory := (ByteMemory.mk []).writeBytes address (List.replicate (8 * count) 255)
  let after := memory.writeBytes address (hintWriteBytes actual)
  (evaluateProgram (do
    HintReadWordChip.stateChannel.push (const (⟨0, 1, Address.ofNat 1, 0, Address.ofNat address⟩ : HintReadWordChip.State Fp))
    HintReadWordChip.stateChannel.pull (const (⟨0, 1, Address.ofNat 1, Address.ofNat count,
      Address.ofNat (address + 8 * (count - 1))⟩ : HintReadWordChip.State Fp))
    Circuit.forEach (Vector.ofFn fun index : Fin count => index.val) fun index => do
      let key := Address.ofNat (p := SP1Prime) (address + 8 * index)
      Channels.memoryChannel.push (const ⟨0, 0, key[0], key[1], key[2], oldWord⟩)
      Channels.memoryChannel.pull (const ⟨0, 2, key[0], key[1], key[2],
        Soundness.Target.bitVecToWord (after.readWord (address + 8 * index))⟩)) []).2

/-- Check all supplied transfer rows against source membership, byte permissions and semantic
endpoints. Omitting one requested permission exercises the unbalanced-demand rejection. -/
def check (image : ProgramImage) (address : ℕ) (actual : Bytes) (rows : List Row)
    (missingPermission : Option ℕ := none) : Bool :=
  let consumers := rows.map checked
  let sources := rows.map fun row => source actual (row.2.step row.1).word
  let permissions := rows.flatMap fun row => (List.range 8).filterMap fun index =>
    let target := Address.toNat row.2.address + index
    if missingPermission == some target then none else some (permission image target)
  consumers.all (·.1) && sources.all (·.1) && permissions.all (·.1) &&
    balanced (boundaries address actual ++ consumers.flatMap (·.2) ++ sources.flatMap (·.2) ++ permissions.flatMap (·.2))

end SP1CleanTest.Core.HintReadFixtures
