import SP1Clean.Proofs.Operations.WriteBufferPhysical
import SP1Clean.Proofs.Completeness.WriteGroupRows
import SP1Clean.Math.SP1Field
import Clean.Circuit.WitnessExport
import ToClean.Air.EnsembleCheck

/-! # Generated AIR and signed-coverage regressions for WRITE buffers

Exercise the actual guarded circuit rows and compare their private interactions against
the original ECALL header and an independent released aligned-word packet.
-/

namespace SP1CleanTest.Core.WriteBuffer
open Circuit SP1Clean SP1Clean.WriteBuffer Soundness.Target Air.Flat

private abbrev F := ZMod SP1Prime

/-- info: exportable ✓ (184 witness cells) -/
#guard_msgs in
#assert_exportable (spanComponent (p := SP1Prime)).circuit

/-- info: exportable ✓ (48 witness cells) -/
#guard_msgs in
#assert_exportable (wordComponent (p := SP1Prime)).circuit

private def natWord (n : ℕ) : Word F := bitVecToWord (BitVec.ofNat 64 n)

private def header (clock address length : ℕ) : WritePacket.Header F :=
  ⟨Address.ofNat clock, natWord 13, natWord address, natWord length⟩

private def byteRange (i : Interaction F) : Bool :=
  if i.channel.name == (Channels.byteChannel (p := SP1Prime)).name && i.mult != 0 then
    match i.msg.toList with
    | [op, value, bits, extra] => i.direction == .pull && op == 6 && value.val < 65536 && bits == 16 && extra == 0
    | _ => false
  else true

private def evalRow (c : Component F) (input : c.Input F) : Bool × List (Interaction F) :=
  let program := c.circuit.main (varFromOffset c.Input 0)
  let env := (program.proverEnvironment (.empty _) (toElements input).toList).toEnvironment
  let ops := (program.operations (size c.Input)).toFlat
  let messages := (FlatOperation.interactions ops).map fun msg => msg.eval env
  let localChecks := ops.all fun op => match op with
    | .assert e => env e == 0
    | .lookup .. => false
    | _ => true
  (localChecks && messages.all byteRange, messages)

private def checkRows (h : WritePacket.Header F) (span : Span F) (rows : List (Step F))
    (expected : List (WriteProbe.Read F)) (effects : WritePacket.Header F := h)
    (observed : List (WriteProbe.Read F) := expected) : Bool :=
  let evaluated := evalRow spanComponent (span, 1) :: rows.map (fun r => evalRow wordComponent (r, 1))
  let ledger := evaluated.flatMap Prod.snd
  let checks (name : String) (boundary : List (Interaction F)) :=
    checkInteractionBalance SP1Prime (boundary ++ ledger.filter fun i => i.channel.name == name)
  evaluated.all Prod.fst &&
    checks (WritePacket.channel (p := SP1Prime)).name [WritePacket.channel.pushedValue h] &&
    checks (channel (p := SP1Prime)).name [] &&
    checks (effectHeaderChannel (p := SP1Prime)).name [effectHeaderChannel.pulledValue effects] &&
    checks (wordChannel (p := SP1Prime)).name (observed.map wordChannel.pulledValue) &&
    checks (WriteProbe.readChannel (p := SP1Prime)).name (expected.map WriteProbe.readChannel.pushedValue)

private def fixture (clock address length : ℕ) : Span F × List (Step F) × List (WriteProbe.Read F) :=
  let h := header clock address length
  let indices := List.range ((address % 8 + length + 7) / 8)
  let rows := indices.map fun i => Step.populate h.clock (address / 8 + i) (natWord (700 + i))
  let reads := indices.map fun i => WriteProbe.Read.mk (Address.ofNat (address - address % 8 + 8 * i)) h.clock (natWord (700 + i))
  (Span.populate h, rows, reads)

/-- Empty aligned calls, the partial word of an empty unaligned slice, normal spans,
and both legal one-past-byte edge cases satisfy the generated assertions and all five private buses. -/
theorem legalBoundaries :
    [(65536, 0, 0), (65543, 0, 1), (65536, 8, 1), (131071, 10, 3),
     (2 ^ 48 - 8, 8, 1), (2 ^ 48 - 1, 1, 1), (2 ^ 48, 0, 0)].all (fun (address, length, n) =>
       let h := header (2 ^ 40 + 9) address length
       let (s, rows, reads) := fixture (2 ^ 40 + 9) address length
       rows.length == n && checkRows h s rows reads) = true := by native_decide

/-- Reordering physical rows preserves the walk. Missing, duplicated, misclocked and
forged reads fail. A substituted address or length fails even when it rounds to the same cells. -/
theorem rejectsMutations :
    let h := header 123 65543 2
    let (s, rows, reads) := fixture 123 65543 2
    let first := rows.head!
    let changedClock := { first with read := { first.read with clock := Address.ofNat 124 } }
    let changedWord := { first with read := { first.read with value := natWord 0 } }
    let changedIndex := { first with next := first.index }
    [checkRows h s rows.reverse reads, checkRows h s rows.tail reads,
     checkRows h s (first :: rows) reads, checkRows h s (changedClock :: rows.tail) reads,
     checkRows h s (changedWord :: rows.tail) reads, checkRows h s (changedIndex :: rows.tail) reads,
     checkRows h (Span.populate (header 123 65542 3)) rows reads,
     checkRows h (Span.populate (header 123 65543 3)) rows reads,
     checkRows h {s with stop := s.first} rows reads] = [true, false, false, false, false, false, false, false, false] := by
  native_decide

/-- The downstream effect receiver must consume the same full header and every observed value. -/
theorem rejectsChangedEffects :
    let h := header 123 65543 2
    let (s, rows, reads) := fixture 123 65543 2
    let r := reads.head!
    [checkRows h s rows reads {h with descriptor := natWord 4},
     checkRows h s rows reads h reads.tail, checkRows h s rows reads h (r :: reads),
     checkRows h s rows reads h ({r with value := natWord 71} :: reads.tail)] = [false, false, false, false] := by
  native_decide

/-- A nonempty slice past guest RAM, a skipped high address bit, and 64-bit addition wrap are rejected. -/
theorem excludesOverflow :
    [(2 ^ 48, 1), (2 ^ 48 - 1, 2), (2 ^ 48 + 1, 0), (65536, 2 ^ 64 - 65536)].all
      (fun (address, length) => !(evalRow spanComponent (Span.populate (header 7 address length), 1)).1) = true := by
  native_decide

private def acrossBlocks : WriteEffects.Group F :=
  let octets : WriteEffects.Octets F := ⟨Address.ofNat 65536, Address.ofNat 17, #v[90,91,92,93,7,8,9,10]⟩
  WriteEffects.Group.populate octets 1 (Address.ofNat 0) 4 4 7 ((List.range 11).map (BitVec.ofNat 8))

/-- An unaligned output crosses at byte seven and ends in a three-byte final block.
Changing the second block's first lane or using its padded fourth lane is rejected. -/
theorem groupedCrossing :
    let row := acrossBlocks
    [(evalRow WriteEffects.groupComponent (row,1)).1,
     (evalRow WriteEffects.groupComponent ({row with right := row.right.set 0 77},1)).1,
     (evalRow WriteEffects.groupComponent ({row with rightSize := 2},1)).1] = [true,false,false] := by
  native_decide

/-- Disabled rows and ignored writes retain both syntactic block occurrences. Only a
nonempty observed destination funds them, even when the input word crosses the boundary. -/
theorem groupedBlockCounts :
    let row := acrossBlocks
    let counts := fun (r : WriteEffects.Group F) (active : F) =>
      ((evalRow WriteEffects.groupComponent (r,active)).2.filter
        (fun e => e.channel.name == (WriteEffects.blockChannel (p := SP1Prime)).name)).map (·.mult)
    let ignored := {row with ignored := 1, previous := {row.previous with sink := 0}}
    counts row 1 = [1,1] ∧ counts row 0 = [0,0] ∧
      (evalRow WriteEffects.groupComponent (ignored,1)).1 = true ∧ counts ignored 1 = [0,0] := by
  native_decide

end SP1CleanTest.Core.WriteBuffer
