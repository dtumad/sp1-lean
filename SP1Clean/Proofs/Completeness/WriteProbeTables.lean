import SP1Clean.Proofs.Completeness.WriteProbeInputs
import SP1Clean.Proofs.Operations.WriteProbeLedger
import ToClean.Air.GuardedDemandTable

/-! # Building the physical native WRITE observation table

Clean builds the row witnesses and pads the actual read demand to its physical height.
The table retains exactly one version pull and one read receipt per row at that row's activity.
-/

namespace SP1Clean.WriteProbe
open Circuit Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Honest physical rows in demand order followed by zero-activity padding. -/
def physicalInputs (inputs : List (Inputs (ZMod p))) : List (RowInput (ZMod p)) :=
  WitnessGeneration.guardedRows inputs

omit [Fact (2 ^ 17 < p)] in
theorem physicalInputs_length (inputs : List (Inputs (ZMod p))) :
    (physicalInputs inputs).length = WitnessGeneration.demandHeight inputs.length := WitnessGeneration.guardedRows_length inputs

/-- Generate the complete demand-padded table with Clean's ordinary row builder and private inputs. -/
def table (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (height : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size) : Table (ZMod p) :=
  let rows := physicalInputs inputs
  Table.ofInputs component rows data ((physicalInputs_length inputs).trans_le height) (fun _ => trivial)

/-- Honest inputs derived from the physical versions produce all flat constraints and guarantees.
No history oracle, dynamic table, or additional trace event is supplied in the prover data. -/
theorem table_complete {inputs : List (Inputs (ZMod p))} (honest : ∀ input ∈ inputs, ProverAssumptions input)
    (data : ProverData (ZMod p)) (height : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size) :
    (table inputs data height).Constraints ∧ (table inputs data height).Guarantees := by
  exact Table.ofInputs_valid (component (p := p)) (physicalInputs inputs) data
    ((physicalInputs_length inputs).trans_le height) (fun _ => trivial)
    (WitnessGeneration.guardedRows_all (F := ZMod p) ProverAssumptions honest)

private theorem table_ledger (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (height : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size) (channel : RawChannel (ZMod p))
    (values : RowInput (ZMod p) → List (Interaction (ZMod p)))
    (point : ∀ env, component.operations.interactionValuesWith channel env =
        values (valueFromOffset RowInput 0 env)) :
    (table inputs data height).interactionsWith channel = (physicalInputs inputs).flatMap values := by
  exact Table.ofInputs_ledger (component (p := p)) (physicalInputs inputs) data
    ((physicalInputs_length inputs).trans_le height) (fun _ => trivial) channel values point

/-- The input-side signed ledger preserves every occurrence, including aliased requests and padding. -/
theorem table_versions (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (height) :
    (table inputs data height).interactionsWith versionChannel.toRaw =
      (physicalInputs inputs).flatMap fun row => [versionChannel.pulledIfValue row.2 row.1.version] := by
  exact table_ledger _ _ _ _ _ component_versions

/-- The complete generated output ledger carries the exact Read message from each active input. -/
theorem table_reads (inputs : List (Inputs (ZMod p))) (data : ProverData (ZMod p)) (height) :
    (table inputs data height).interactionsWith readChannel.toRaw =
      (physicalInputs inputs).flatMap fun row => [readChannel.pushedIfValue row.2 row.1.read] := by
  exact table_ledger _ _ _ _ _ component_reads

/-- Batch lookup retains the caller's order and repeated requests. Each request carries a
physical execution cut and the concrete source location to inspect at that cut. -/
def inputsAt? (snapshot : Semantics.MemorySnapshot) (rows : List (Semantics.RowFacts p)) (clock : ℕ → ℕ)
    (requests : List (ℕ × Semantics.MemLoc)) : Option (List (Inputs (ZMod p))) :=
  requests.mapM fun (cut, loc) => inputAt? snapshot rows loc (clock cut)

private theorem collect {α β : Type} (f : α → Option β) (rel : α → β → Prop) (honest : β → Prop)
    (requests : List α) (available : ∀ a ∈ requests, ∃ b, f a = some b ∧ honest b ∧ rel a b) :
    ∃ inputs, requests.mapM f = some inputs ∧ List.Forall₂ rel requests inputs ∧ ∀ b ∈ inputs, honest b := by
  induction requests with
  | nil => exact ⟨[], rfl, .nil, by simp⟩
  | cons a rest ih =>
    obtain ⟨b, head, good, response⟩ := available a List.mem_cons_self
    obtain ⟨tail, found, paired, valid⟩ := ih (fun a m => available a (List.mem_cons_of_mem _ m))
    refine ⟨b :: tail, by simp [List.mapM_cons, head, found], .cons response paired, ?_⟩
    intro x member
    rcases List.mem_cons.mp member with rfl | occurs
    · exact good
    · exact valid x occurs

open Semantics Soundness

/-- Construct a demand-padded physical table for any finite list of legal read-only probes on
a checked installed prefix. Every receipt matches its actual replay cut. The only size bound
is the physical table index; shard packet accounting gives the stronger `2^28` bound. -/
theorem installed_table {q : ℕ} [Fact q.Prime] [Fact (2 ^ 25 < q)] [Fact (2 ^ 17 < q)]
    {extra : List (Component (ZMod q))} [GroundingResources extra]
    {image : ProgramImage} {source : ExecutionSnapshot} {final : HostHintQueue.State (ZMod q)}
    {bankFinal : HostState} {channels : List (RawChannel (ZMod q))}
    [HostFinalMemory.Registration image source extra HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints) channels]
    {names : HostFinalMemory.UniqueNames image source extra HostCallReceivers.available
      (HostHintReadLocal.sourceResources source.host.io.hints)}
    (witness : HostHintQueueBoundary.SourceWitness image source final bankFinal extra channels names)
    (checked : witness.Constraints) (balanced : HostHintQueueBoundary.Balanced witness) (data : ProverData (ZMod q)) :
    ∃ (valid : image.Valid) (carrier : HostHintReadCPU.GroundingCarrier witness),
      ∀ (requests : List (ℕ × MemLoc)), (∀ r ∈ requests, r.1 ≤ carrier.ordered.length ∧
        ValidKey r.2.busAddress ∧ carrier.timeline.start r.1 < 2 ^ 48) →
        WitnessGeneration.demandHeight requests.length ≤ UInt64.size →
        ∃ inputs height, inputsAt? source.sail.memorySnapshot (TraceGen.WriteObservations.physicalRows carrier)
            carrier.timeline.start requests = some inputs ∧
          List.Forall₂ (fun (r : ℕ × MemLoc) (i : Inputs (ZMod q)) =>
            i.read.key = Address.ofNat r.2.busAddress ∧ i.read.clock = Address.ofNat (carrier.timeline.start r.1) ∧
            ∃ s, carrier.pairedTrajectory valid r.1 = some s ∧ locContent s.sail r.2 = some i.read.value.toBitVec64)
            requests inputs ∧ (table inputs data height).Constraints ∧ (table inputs data height).Guarantees := by
  obtain ⟨valid, carrier, each⟩ := installed_inputs witness checked balanced
  refine ⟨valid, carrier, fun requests domain fits => ?_⟩
  let f := fun (r : ℕ × MemLoc) => inputAt? source.sail.memorySnapshot (TraceGen.WriteObservations.physicalRows carrier)
    r.2 (carrier.timeline.start r.1)
  let rel := fun (r : ℕ × MemLoc) (i : Inputs (ZMod q)) =>
    i.read.key = Address.ofNat r.2.busAddress ∧ i.read.clock = Address.ofNat (carrier.timeline.start r.1) ∧
    ∃ s, carrier.pairedTrajectory valid r.1 = some s ∧ locContent s.sail r.2 = some i.read.value.toBitVec64
  have available r (member : r ∈ requests) : ∃ input, f r = some input ∧ ProverAssumptions input ∧ rel r input := by
    obtain ⟨cut, key, clock⟩ := domain r member
    obtain ⟨s, reached, one⟩ := each r.1 cut
    obtain ⟨input, found, honest, address, time, value⟩ := one r.2 key clock
    exact ⟨input, found, honest, address, time, s, reached, value⟩
  obtain ⟨inputs, found, paired, honest⟩ := collect f rel ProverAssumptions requests available
  have height : WitnessGeneration.demandHeight inputs.length ≤ UInt64.size := paired.length_eq ▸ fits
  exact ⟨inputs, height, found, paired, table_complete honest data height⟩

end SP1Clean.WriteProbe
