import SP1Clean.Proofs.Operations.WriteProbeLedger
import SP1Clean.Math.SP1Field
import Clean.Circuit.WitnessExport
import Clean.Air.WitnessGeneration

/-! # Native WRITE read-only observer regressions

Evaluate generated witness cells and the actual flattened assertions. Compare both physical
messages with an independently fixed version supply and host request. The arithmetic row alone
cannot identify an upstream value; changing both value columns still fails the private ledger.
-/

namespace SP1CleanTest.Core.WriteProbe

open Circuit SP1Clean SP1Clean.WriteProbe

private abbrev F := ZMod SP1Prime

/-- info: exportable ✓ (346 witness cells) -/
#guard_msgs in
#assert_exportable (guarded (p := SP1Prime))

private def version (key lower upper : ℕ) (value : Word F) : Version F :=
  ⟨Address.ofNat key, Address.ofNat lower, Address.ofNat upper, value⟩

private def read (key clock : ℕ) (value : Word F) : Read F := ⟨Address.ofNat key, Address.ofNat clock, value⟩

/-- Check the actual AIR assertions and the two expected signed messages. -/
private def evaluate (input : RowInput F) (supplied : Version F) (requested : Read F) (expectedMultiplicity : F := 1) :
    Bool × Bool :=
  let program := guarded.main (varFromOffset RowInput 0)
  let env := (program.proverEnvironment (.empty _) (toElements input).toList).toEnvironment
  let operations := (program.operations (size RowInput)).toFlat
  let assertions := operations.all fun op => match op with
    | .assert eq => env eq == 0
    | .lookup .. => false
    | _ => true
  let messages : List (String × Channel.Direction × F × Array F) := (FlatOperation.interactions operations).map fun abstract =>
    let actual := abstract.eval env
    (actual.channel.name, actual.direction, actual.mult, actual.msg)
  (assertions, messages == [((versionChannel (p := SP1Prime)).name, .pull, expectedMultiplicity, (toElements supplied).toArray),
    ((readChannel (p := SP1Prime)).name, .push, expectedMultiplicity, (toElements requested).toArray)])

private def check (candidate : Version F) (time : ℕ) (supplied : Version F) (requested : Read F) : Bool × Bool :=
  evaluate (populate candidate (Address.ofNat time), 1) supplied requested

private def held : Word F := #v[7, 11, 23, 65535]
private def forged : Word F := #v[7, 11, 24, 65535]

/-- Genesis includes zero. Both interior endpoints and the final 48-bit clock are accepted. -/
theorem acceptsLegalProbes :
    [(12, 0, 15, 0), (65536, 17, 32, 17), (65536, 17, 32, 32),
     (2 ^ 48 - 8, 2 ^ 24, 2 ^ 48 - 1, 2 ^ 48 - 1)].all (fun (key, lo, hi, clock) =>
      let v := version key lo hi held
      check v clock v (read key clock held) == (true, true)) = true := by native_decide

/-- A later genuine interval, a reversed interval, misaligned RAM, another register, and
noncanonical clock/value limbs fail even when the advertised supply matches the row. -/
theorem rejectsMalformedRows :
    let ram := version 65536 17 32 held
    let badWord := version 65536 17 32 #v[7, 11, 23, 65536]
    let badClock : fields 3 F := #v[65553, 0, 0]
    [!(check ram 16 ram (read 65536 16 held)).1,
     !(check (version 65536 33 17 held) 24 ram (read 65536 24 held)).1,
     !(check (version 65537 17 32 held) 24 ram (read 65537 24 held)).1,
     !(check (version 11 17 32 held) 24 ram (read 11 24 held)).1,
     !(evaluate ({ populate ram (Address.ofNat 24) with quotients := #v[1, 0, 0] }, 1) ram (read 65536 24 held)).1,
     !(check badWord 24 badWord (read 65536 24 badWord.value)).1,
     !(evaluate (populate ram badClock, 1) ram ⟨ram.key, badClock, held⟩).1,
     !(evaluate (populate ram (Address.ofNat 24), 2) ram (read 65536 24 held)).1].all id = true := by
  native_decide

/-- A disabled row retains the two correctly shaped occurrences with zero weight, even when
its unconstrained payload would fail an active address and clock check. -/
theorem paddingEmitsZeroWeight :
    let unused := version 11 33 17 forged
    evaluate (populate unused (Address.ofNat 42), 0) unused (read 11 42 forged) 0 = (true, true) := by
  native_decide

/-- A well-formed alternate value or shifted clock is caught by the full private receipts.
Replacing the claimed version endpoints also changes the required version message. -/
theorem rejectsForgedJoins :
    let correct := version 65536 17 32 held
    let other := version 65536 17 32 forged
    [check other 23 correct (read 65536 23 forged),
     check correct 24 correct (read 65536 23 held),
     check (version 65536 16 32 held) 23 correct (read 65536 23 held)] =
      [(true, false), (true, false), (true, false)] := by native_decide

/-- Run the registered demand guard with actual private index pages and canonical row inputs. -/
private def routing (request : Read F) : Except String Bool := do
  let clock : UInt64 := 2 ^ 32 + 17
  let ram : UInt64 := 2 ^ 40 + 8
  let input (key time : UInt64) (value : Word F) : RowInput F :=
    (populate (version key.toNat 0 (2 ^ 48 - 1) value) (Address.ofNat time.toNat), 1)
  let indexed ← Witgen.HintIndex.prepareKeys (Input := RowInput)
    [([clock, 12], input 12 clock held), ([clock, ram], input ram clock forged),
     ([clock + 1, ram], input ram (clock + 1) held)]
  let name := (guarded (p := SP1Prime)).name
  let hints : ProverHint F := Air.Flat.WitnessGeneration.readNamedRows [
    (name ++ ".index", .ofRows (indexed.index.map (·.toArray)) 1),
    (name, .ofRows (indexed.inputs.map (·.toArray)) (size RowInput))]
  match generation (p := SP1Prime) with
  | .demand mode => pure (mode.accepts
      ⟨(readChannel (p := SP1Prime)).name, (toElements request).toArray, -1⟩ (.empty F) hints)
  | .preallocated _ => throw "expected one row per probe request"

/-- Actual Clean routing distinguishes both high-limb keys, both high-limb clocks, and a
forged payload with the correct key and clock. The absent row cannot answer a zero-word demand. -/
theorem routesFullReceipt :
    let clock := 2 ^ 32 + 17
    let ram := 2 ^ 40 + 8
    ([read 12 clock held, read ram clock forged, read ram (clock + 1) held, read ram clock held,
      read 12 (clock + 1) 0, read (ram + 8) clock 0].mapM routing) =
      .ok [true, true, true, false, false, false] := by native_decide

end SP1CleanTest.Core.WriteProbe
