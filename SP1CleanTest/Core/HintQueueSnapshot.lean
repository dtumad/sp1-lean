import SP1Clean.Native.Operations.HintQueueSeal
import SP1Clean.Proofs.Operations.HintQueueSnapshot
import SP1Clean.Math.SP1Field
import ToClean.Air.EnsembleCheck
import ToClean.Air.TableBuild

/-! # Authenticating a surviving fresh hint and the complete older suffix -/

namespace SP1CleanTest.Core.HintQueueSnapshot
open SP1Clean Semantics Semantics.HintQueue Circuit Air.Flat HostHintSnapshot

private abbrev F := ZMod SP1Prime
private def source : List Bytes := [[99], [], [202]]
private def added : Bytes := [8,7,6,5,4,3,2,1]
private def target : List Bytes := [added, [], [202]]

-- Source node 3 is popped. Fresh node 4 points at node 2, and the live queue has length 3.
private def store := (prepend (ofList source).1 2 [added]).1
private def actual : HostHintQueue.State F := HostHintQueue.State.encode 512 4 4

example : decode? store 4 = some target ∧ store.size = 4 ∧ target.length = 3 := by native_decide

private def evaluated (c : Component F) (input : c.Input F) : Bool × List (Interaction F) :=
  let data := ProverData.empty F
  let row := c.buildRow input data (.empty F)
  let env := Environment.fromArray row data
  let ops := c.operations
  ((ops.constraints.all fun constraint => env constraint == 0) && ops.lookups.isEmpty,
    ops.interactions.map (·.eval env))

private def link (head tail : ℕ) : Links F := ⟨Address.ofNat head, Address.ofNat tail⟩

private def inputs : List (Inputs F) :=
  (schedule target).zipWith (fun s ptr => (s, ptr, 1)) [link 4 2, link 4 2, link 2 1, link 1 0]

private def check (rows : List (Inputs F)) (terminal : HostHintQueue.State F) : Bool := Id.run do
  let reader := component (p := SP1Prime) target
  let fixed := reader.FixedRowsMatch (rows.map fun r => reader.buildRow r (.empty F) (.empty F))
  let all := rows.map (evaluated reader) ++ [evaluated (Seal.component target) (1, terminal, 1)]
  let ledger := all.flatMap Prod.snd
  let balanced (name : String) (external : List (Interaction F)) :=
    checkInteractionBalance SP1Prime (external ++ ledger.filter (fun i => i.channel.name == name))
  let nodes := [4, 2, 1].filterMap fun head =>
    (node? store head).map fun node => HostHintQueue.nodeChannel.pushedValue (NodeRecord.encode head node)
  let words := [4, 2, 1].flatMap fun head =>
    (node? store head).toList.flatMap fun node => (nodeWordRows (p := SP1Prime) head node.bytes).map
      HostHintQueue.wordChannel.pushedValue
  return decide fixed && all.all Prod.fst && balanced (channel (p := SP1Prime)).name [] &&
    balanced (HostHintQueue.nodeChannel (p := SP1Prime)).name nodes &&
    balanced (HostHintQueue.wordChannel (p := SP1Prime)).name words &&
    balanced (HostHintQueue.stateChannel (p := SP1Prime)).name
      [HostHintQueue.stateChannel.pushedValue actual, HostHintQueue.stateChannel.pulledValue (HostHintQueueBoundary.initial target)]

/-- The extra aligned-padding word is mandatory, the fresh pointer differs from the public queue
length, and changing a pointer, fixed value, multiplicity or ordered occurrence is detectable. -/
example : check inputs actual = true ∧
    check (inputs.eraseIdx 1) actual = false ∧
    check inputs (HostHintQueue.State.encode 512 3 4) = false ∧
    check (inputs.modify 1 (fun (s, _, count) => (s, link 4 1, count))) actual = false ∧
    check (inputs.modify 0 (fun (s, links, count) => ({s with length := 0}, links, count))) actual = false ∧
    check (inputs.modify 2 (fun (s, links, _) => (s, links, 0))) actual = false := by native_decide

end SP1CleanTest.Core.HintQueueSnapshot
