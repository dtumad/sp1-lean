import SP1Clean.Proofs.Chips.WritePacket.Ledger
import SP1Clean.Proofs.Operations.WriteProbeLedger
import SP1Clean.Native.Operations.WriteProbeRegisterBoundary
import SP1Clean.Proofs.Completeness.MixedSyscallInstruction
import SP1Clean.Proofs.Chips.HostCallChip.Formal
import SP1Clean.Math.SP1Field
import ToClean.Air.EnsembleCheck
import ToClean.Air.TableBuild

/-! # Physical WRITE joins at the incoming ECALL

Use the production instruction builder, the verifier-fixed source register, the probe and the
packet component. The checks read the actual generated rows and apply Clean's count-bounded
LogUp check to each of the four handoff channels, including unused fixed-source occurrences.
-/

namespace SP1CleanTest.WritePacketHandoff

open Circuit Air.Flat SP1Clean SP1Clean.Machine SP1Clean.Semantics SP1Clean.TraceGen

private abbrev F := ZMod SP1Prime

private def cpu : Component F where
  circuit := HostCallChip.circuit
  generation := HostCallChip.generation
  Assumptions := HostCallChip.circuit.Assumptions

private def start : Nat := 2 ^ 32 + 2 ^ 24 + 1

private def registers (length : BitVec 64) : MemorySnapshot :=
  ⟨(Vector.replicate 32 0).set 12 length, ⟨[]⟩⟩

private def event (clock : Nat) : CoreSyscallEvent :=
  ⟨clock, 0x10000, 0x10004, 2, 13, 0x10009, 2⟩

private def build (component : Component F) (input : component.Input F) : Environment F :=
  Environment.fromArray (component.buildRow input (.empty _) (ProverHint.empty _)) (.empty _)

private def emitted (component : Component F) (input : component.Input F) (channel : RawChannel F) :
    List (Interaction F) :=
  (component.rowOperations.interactionValues (build component input)).filter (fun i => i.channel.name == channel.name)

/-- Both observation components use only assertions and channels. -/
private def checked (component : Component F) (input : component.Input F) : Bool :=
  let env := build component input
  component.rowOperations.toFlat.all fun operation => match operation with
    | .assert eq => env eq == 0
    | .lookup .. => false
    | _ => true

private def packetClock (t : Nat) : ClockParts F :=
  .split ((t / 2 ^ 24 : Nat) : F) ((t % 2 ^ 24 : Nat) : F)

private def joins (packetTime probeTime : Nat) (observed length : BitVec 64) : List Bool := Id.run do
  let row := syscallInstruction (p := SP1Prime) AccessFrontier.initial (event start)
  let call := HostCallChip.message row
  let packet : WritePacket.Inputs F := ⟨packetClock packetTime, call.arg1, call.arg2, Soundness.Target.bitVecToWord length⟩
  let src := registers 9
  let dst := registers 17
  let fixed := WriteProbe.registerBoundaries (p := SP1Prime) src dst start (start + 264)
  let provider := WriteProbe.registerBoundaryComponent (p := SP1Prime) src dst start (start + 264)
  let version := WriteProbe.incomingX12 (p := SP1Prime) (registers observed) start
  let probe := WriteProbe.populate version (Address.ofNat probeTime)
  let demand := WriteProbe.component (p := SP1Prime)
  let bind := WritePacket.component (p := SP1Prime)
  let v := (WriteProbe.versionChannel (p := SP1Prime)).toRaw
  let r := (WriteProbe.readChannel (p := SP1Prime)).toRaw
  let h := (HostCallChip.channel (p := SP1Prime)).toRaw
  let pk := (WritePacket.channel (p := SP1Prime)).toRaw
  let expected : WritePacket.Header F := ⟨Address.ofNat start, #v[13, 0, 0, 0], #v[9, 1, 0, 0], #v[9, 0, 0, 0]⟩
  return [
    checked bind (packet, 1) && checked demand (probe, 1),
    checkInteractionBalance SP1Prime (emitted cpu row h ++ emitted bind (packet, 1) h),
    checkInteractionBalance SP1Prime (emitted demand (probe, 1) r ++ emitted bind (packet, 1) r),
    checkInteractionBalance SP1Prime (emitted provider (fixed.fixedEntry 0, 1) v ++
      emitted provider (fixed.fixedEntry 1, 0) v ++ emitted demand (probe, 1) v),
    checkInteractionBalance SP1Prime (emitted bind (packet, 1) pk ++ [WritePacket.channel.pulledValue expected])]

example : joins start start 9 9 = [true, true, true, true, true] := by native_decide
example : joins start start 17 17 = [true, true, true, false, false] := by native_decide
example : joins start start 37 37 = [true, true, true, false, false] := by native_decide
example : joins (start + 264) (start + 264) 9 9 = [false, false, true, true, false] := by native_decide
example : joins start (start + 264) 9 9 = [false, true, false, true, true] := by native_decide

end SP1CleanTest.WritePacketHandoff
