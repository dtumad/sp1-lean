import SP1Clean.Proofs.Chips.HostRamReadChip.Ledger
import SP1Clean.Proofs.Chips.HostRamReadChip.Populate
import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport

/-! # Host-buffer read regressions

Run compiled provider rows against a WRITE span's requested cells. Physical Memory accesses
remain unique. Authenticating the span through an installed host-call table remains separate.
-/

namespace SP1CleanTest.Core.HostRamRead

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target HostChecks

private abbrev Fp := ZMod SP1Prime

private def prior (cell : ℕ) : Channels.MemoryMsg Fp :=
  let address : Word Fp := bitVecToWord (BitVec.ofNat 64 (cell * 8))
  ⟨0, 16777215, address[0], address[1], address[2],
    #v[(cell % 65536 : ℕ), 65535, 257, 32768]⟩

private def evaluate (input : HostRamReadChip.Inputs Fp) (corrupt : Option ℕ := none) :
    Bool × Ledger :=
  evaluateProgram (HostRamReadChip.main (varFromOffset HostRamReadChip.Inputs 0))
    (toElements input).toList corrupt

private def requests (span : MemorySpan) : Ledger :=
  span.cells.map fun cell =>
    let record := prior cell
    ("sp1.native.host_ram_read",
      [1, 1, record.addr0, record.addr1, record.addr2] ++ record.value.toList, -1)

private def balanced (ledger : Ledger) : Bool :=
  ledger.length < SP1Prime && ledger.all fun (channel, message, _) =>
    (ledger.filterMap fun (otherChannel, otherMessage, mult) =>
      if channel == otherChannel && message == otherMessage then some mult else none).sum == 0

private def rows (span : MemorySpan) : List (HostRamReadChip.Inputs Fp) :=
  HostRamReadChip.populateSpan span prior 1 1 0

private def ledger (inputs : List (HostRamReadChip.Inputs Fp)) : Ledger :=
  inputs.flatMap fun input => (evaluate input).2

private def readBalanced (inputs : List (HostRamReadChip.Inputs Fp))
    (span : MemorySpan) : Bool :=
  balanced (((ledger inputs).filter fun entry => entry.1 == "sp1.native.host_ram_read") ++
    requests span)

private def spansValid (span : MemorySpan) : Bool :=
  let inputs := rows span
  let interactions := ledger inputs
  let memory := interactions.filter fun entry => entry.1 == "SP1Memory"
  let pushes := memory.filter fun entry => entry.2.2 == 1
  inputs.all (fun input => (evaluate input).1) && readBalanced inputs span &&
    balanced (interactions.filter fun entry => entry.1 == "sp1.native.host_ram_access") &&
    memory.length == 2 * span.cells.length &&
    (pushes.map fun entry => entry.2.1.drop 2 |>.take 3).eraseDups.length == pushes.length &&
    memory.all (fun entry => entry.2.2 == 1 || entry.2.2 == -1)

/-- Empty, unaligned, cross-word and upper-bound buffers use the actual RAM circuit. -/
theorem compiledSpans :
    [⟨2 ^ 48, 0⟩, ⟨65539, 17⟩, ⟨65536, 32⟩, ⟨65539, 32⟩, ⟨2 ^ 48 - 32, 32⟩].all
      spansValid = true := by native_decide

/-- Every read produces one logical message and one physical Memory pair. -/
theorem readLedger :
    let input := HostRamReadChip.populate (prior 8192) 1 1 0
    let interactions := (evaluate input).2
    ((interactions.filter fun entry => entry.1 == "sp1.native.host_ram_read").map
      fun entry => entry.2.2) = [1] ∧
    ((interactions.filter fun entry => entry.1 == "SP1Memory").map
      fun entry => entry.2.2) = [-1, 1] := by native_decide

/-- Writes, malformed words, and corrupted witness cells are rejected. -/
theorem rejectsMalformed :
    let input := HostRamReadChip.populate (prior 8192) 1 1 0
    [{ input with ram := { input.ram with new_value := #v[0, 0, 0, 0] } },
      HostRamReadChip.populate { (prior 8192) with value := #v[65536, 0, 0, 0] } 1 1 0].all
      (fun row => !(evaluate row).1) = true ∧
    [0, 64, 200].all (fun cell => !(evaluate input (some cell)).1) = true := by native_decide

/-- Locally valid missing and duplicate rows fail the single-buffer read ledger. -/
theorem rejectsWrongMultiplicity :
    let span : MemorySpan := ⟨65539, 32⟩
    let inputs := rows span
    inputs.all (fun input => (evaluate input).1) = true ∧
    readBalanced inputs.tail span = false ∧ readBalanced (inputs ++ inputs) span = false := by
  native_decide

/-- Payload and event-clock changes remain visible even when each altered row is locally valid. -/
theorem rejectsWrongReads :
    let span : MemorySpan := ⟨65539, 32⟩
    let wrongWord := HostRamReadChip.populateSpan span
      (fun cell => { (prior cell) with value := #v[0, 0, 0, 0] }) 1 1 0
    let wrongClock := HostRamReadChip.populateSpan span prior 1 9 0
    wrongWord.all (fun input => (evaluate input).1) = true ∧
    wrongClock.all (fun input => (evaluate input).1) = true ∧
    readBalanced wrongWord span = false ∧ readBalanced wrongClock span = false ∧
    readBalanced (rows span).tail span = false := by native_decide

/-- info: exportable ✓ (201 witness cells) -/
#guard_msgs in
#assert_exportable (HostRamReadChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.HostRamRead
