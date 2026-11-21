import SP1Clean.FormalModel.Contracts.SailBoundary

/-! # Dynamic Sail bookkeeping at the supplied shard endpoint -/

namespace SP1Clean.Soundness.Shard

open Machine Semantics
open LeanRV64D (Register)

/-- The supplied target's dynamic Sail bookkeeping agrees with the trace's: nextPC, the
retirement flag and count, the interrupt refresh and the written event index. -/
structure DynamicMatch (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop where
  nextPC : target.sail.registers.get? Register.nextPC =
    nextPcAfter events (source.sail.registers.get? Register.nextPC) (some target.pc)
  increment : target.sail.registers.get? Register.minstret_increment =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.minstret_increment
      else some (retirementEnabled source.sail.realize)
  retired : target.sail.registers.get? Register.minstret =
    (source.sail.registers.get? Register.minstret).map (fun value => value + BitVec.ofNat 64
      (if retirementEnabled source.sail.realize then events.countP ExecutionEvent.isOrdinary else 0))
  interrupts : target.sail.registers.get? Register.mip =
    if events.countP ExecutionEvent.isOrdinary = 0 then source.sail.registers.get? Register.mip
      else some (TryStepReduction.refreshedMip source.sail.realize)
  eventIndex : target.sail.registers.get? Register.written_event_index =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.written_event_index else some none

end SP1Clean.Soundness.Shard
