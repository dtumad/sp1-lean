import SP1Clean.Native.Operations.InitialMemoryRead
import SP1Clean.Math.SP1Field

/-! # Physical directions of the eight fixed interval lookups in a snapshot word read

The source and target byte reads preserve each lookup's pull direction. Byte arithmetic may
only use its own declared channels, independently of the incoming word and witness offsets.
-/

namespace SP1Clean.SnapshotReadDirections

open Circuit Air.Flat Semantics

private abbrev F := ZMod SP1Prime

/-- The fixed interval name selected by each original snapshot checker. -/
def name (target : Bool) : String :=
  if target then "sp1.native.target_memory" else "sp1.native.initial_memory"

/-- An occurrence on this fixed interval channel can only be a pull. -/
def allowed (target : Bool) (a : AbstractInteraction F) : Bool :=
  a.direction == .pull || a.channel.name != name target

/-- A child circuit whose declared channels exclude this private name cannot publish there. -/
theorem otherChannels (target : Bool) {I O : TypeMap} [ProvableType I] [ProvableType O]
    (c : FormalCircuitBase F I O) (free : c.channels.all (fun ch => ch.name != name target) = true)
    (i : Var I F) (n : ℕ) : ((c.main i).operations n).interactions.all (allowed target) = true := by
  apply List.all_eq_true.mpr
  intro a present
  have member : a.channel ∈ c.channels := c.channels_subset i n (List.mem_map.mpr ⟨a,present,rfl⟩)
  simp only [allowed, List.all_eq_true.mp free a.channel member, Bool.or_true]

private theorem lookupAllowed (target : Bool) (memory : ByteMemory) (i : Var Word F) (n : ℕ) :
    ((InitialMemoryLookup.main memory (2^48) i (name target)).operations n).interactions.all (allowed target) = true := by
  have range (i : Var Word F) (n : ℕ) : ((WordRangeCheck.circuit.main i).operations n).interactions.all (allowed target) = true :=
    otherChannels target WordRangeCheck.circuit.base (by cases target <;> rfl) i n
  have cmp (i : Var LtOperationUnsigned.Inputs F) (n : ℕ) : ((LtOperationUnsigned.circuit.main i).operations n).interactions.all (allowed target) = true :=
    otherChannels target LtOperationUnsigned.circuit.base (by cases target <;> rfl) i n
  simp only [InitialMemoryLookup.main, circuit_norm, FormalAssertion.toSubcircuit_interactions, List.all_append, range, cmp, List.all_cons]
  rfl

/-- All eight private interval reads retain pull direction at either snapshot boundary. -/
theorem wordAllowed (target : Bool) (memory : ByteMemory) (i : Var Word F) (n : ℕ) :
    ((InitialMemoryRead.main memory i (name target)).operations n).interactions.all (allowed target) = true := by
  have add (i : Var AddOperation.Inputs F) (n : ℕ) : ((AddOperation.circuit.main i).operations n).interactions.all (allowed target) = true :=
    otherChannels target AddOperation.circuit.base (by cases target <;> rfl) i n
  simp only [InitialMemoryRead.main, circuit_norm, FormalAssertion.toSubcircuit_interactions, GeneralFormalCircuit.toSubcircuit_interactions,
    InitialMemoryLookup.circuitNamed, List.all_append, lookupAllowed, List.all_flatten]
  apply List.all_eq_true.mpr
  intro ls inside
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp inside
  simp only [List.all_append, add, lookupAllowed, Bool.and_self]

end SP1Clean.SnapshotReadDirections
