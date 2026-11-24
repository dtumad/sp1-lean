import SP1Clean.Proofs.Completeness.WriteDestination

/-! # Adjacent WRITE calls sharing one public destination block -/

namespace SP1CleanTest.WriteDestination

open SP1Clean SP1Clean.Semantics SP1Clean.WriteEffects

/-- Seven bytes from an earlier call and four from the next call occupy two
stdout blocks. Both calls must ask for the same first public block. -/
private def sharedBlock : Bool := Id.run do
  let out : WriteStreams := { stdout := [1,2,3,4,5,6,7,8,9,10,11] }
  let prior : WriteStreams := { stdout := [1,2,3,4,5,6,7] }
  let make (earlier : WriteStreams) (clock address length : Nat) (buffer : List (BitVec 64)) :=
    packetGroups clock address length (1 : ZMod SP1Prime) (Address.ofNat 0) buffer
      (destinationOffset .stdout earlier) (destinationBytes .stdout earlier out [])
  let [first] := make {} 8 0x10001 7 [0x0706050403020100] | return false
  let [second] := make prior 16 0x20004 4 [0x0b0a090800000000] | return false
  return first.block false == encodeBlock .stdout out.stdout 0 &&
    second.block false == first.block false && second.block true == encodeBlock .stdout out.stdout 1 &&
    first.rightGate == 0 && second.leftGate == 1 && second.rightGate == 1 &&
    Address.toNat second.previous.position == 7 && Address.toNat second.nextPosition == 11

example : sharedBlock = true := by native_decide

end SP1CleanTest.WriteDestination
