import SP1Clean.Proofs.Operations.WriteMetadataRows
import SP1Clean.Proofs.Completeness.WriteEffectAssembly
import SP1Clean.Proofs.Completeness.WriteAllocationSix

/-! # All physical WRITE metadata reads

Hook dispatches read three metadata records. Each returned buffer reads its own length, including
zero-length buffers. Direct allocations and disabled padding retain their zero-weight occurrences.
-/

namespace SP1Clean.WriteEffects.Witness.Metadata
open Circuit Air.Flat WitnessGeneration WriteAllocation
private abbrev F := ZMod SP1Prime

private def dispatchValues (r : Dispatch F × F) :=
  r.1.metadataReads.map (recordChannel.pulledIfValue (r.2 * r.1.flags.hook))

private def stepValues (r : Step F × F) :=
  [recordChannel.pulledIfValue (r.2 * (1-r.1.direct)) r.1.metadata]

/-- Active records demanded by a dispatcher or fresh allocation, in physical input order. -/
def requests {Row : Type} (rows : List Row) (keys : Row → List (Record F)) (on : Row → F) : List (Record F) :=
  rows.flatMap fun r => if on r = 1 then keys r else []

/-- The exact active dispatch and returned-length packets funded by the fixed table. -/
def records (entries : List Entry) : List (Record F) :=
  requests (inputs entries).dispatches Dispatch.metadataReads (fun r => r.flags.hook) ++
    requests (inputs entries).nodes (fun r => [r.metadata]) (fun r => 1-r.direct)

/-- Three gated records on every physical dispatch row. -/
theorem dispatch_table (rows : List (Dispatch F)) (data : ProverData F) (fit) :
    (dispatchTable rows data fit).interactionsWith recordChannel.toRaw = (guardedRows rows).flatMap dispatchValues :=
  Table.ofInputs_ledger dispatchComponent (guardedRows rows) data ((guardedRows_length rows).trans_le fit)
    (fun _ => trivial) recordChannel.toRaw dispatchValues dispatch_metadata_at

/-- One gated returned-length record on every physical allocation step. -/
theorem step_table (rows : List (Step F)) (data : ProverData F) (fit) :
    (stepTable rows data fit).interactionsWith recordChannel.toRaw = (guardedRows rows).flatMap stepValues :=
  Table.ofInputs_ledger stepComponent (guardedRows rows) data ((guardedRows_length rows).trans_le fit)
    (fun _ => trivial) recordChannel.toRaw stepValues step_metadata_at

private theorem pull_off (keys : List (Record F)) (msg : Array F) :
    balanceOf (keys.map (recordChannel.pulledIfValue 0)) msg = 0 := by
  induction keys with
  | nil => rfl
  | cons k ks ih =>
    rw [List.map_cons,balanceOf_cons,ih,add_zero]
    simp [Channel.pulledIfValue,Interaction.signedMult]

private theorem request_sum {Row : Type} [Zero Row] (rows : List Row) (keys : Row → List (Record F)) (on : Row → F)
    (boolean : ∀ r ∈ rows, IsBool (on r)) (msg : Array F) :
    balanceOf ((guardedRows rows).flatMap (fun r => (keys r.1).map (recordChannel.pulledIfValue (r.2*on r.1)))) msg =
      balanceOf ((requests rows keys on).map recordChannel.pulledValue) msg := by
  rw [guardedRows_balanceOf _ _ _ (by simpa using pull_off (keys 0) msg)]
  simp only [one_mul,requests,List.map_flatMap]
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    rw [List.flatMap_cons,List.flatMap_cons,balanceOf_append,balanceOf_append,ih (fun x used => boolean x (List.mem_cons_of_mem r used))]
    rcases boolean r List.mem_cons_self with off | live
    · simp only [off,zero_ne_one,↓reduceIte,List.map_nil,pull_off,show balanceOf ([] : List (Interaction F)) msg = 0 from rfl,zero_add]
    · simp only [live,↓reduceIte]
      rfl

/-- The two original physical tables debit precisely all funded records, regardless of how
many disabled real-route and padding sites occur. -/
theorem signed_clients (entries : List Entry) (valid : (inputs entries).Valid) (data : ProverData F) (df sf) (msg : Array F) :
    balanceOf ((dispatchTable (inputs entries).dispatches data df).interactionsWith recordChannel.toRaw ++
      (stepTable (inputs entries).nodes data sf).interactionsWith recordChannel.toRaw) msg =
      balanceOf ((records entries).map recordChannel.pulledValue) msg := by
  rw [dispatch_table,step_table,balanceOf_append,records,List.map_append,balanceOf_append]
  apply congrArg₂ (· + ·)
  · exact request_sum _ _ _ (fun r used => (valid.dispatches r used).allocation_gates.1) msg
  · apply request_sum _ (fun r : Step F => [r.metadata]) (fun r => 1-r.direct) _ msg
    intro r used
    rcases (valid.nodes r used).1 with h | h <;> simp [h,IsBool]

/-- Padding is counted by its real physical width in both clients. -/
theorem client_count (entries : List Entry) (data : ProverData F) (df sf) :
    (((dispatchTable (inputs entries).dispatches data df).interactionsWith recordChannel.toRaw) ++
      (stepTable (inputs entries).nodes data sf).interactionsWith recordChannel.toRaw).length =
      3 * demandHeight (inputs entries).dispatches.length + demandHeight (inputs entries).nodes.length := by
  rw [dispatch_table,step_table,List.length_append]
  have dispatches (xs : List (Dispatch F × F)) : (xs.flatMap dispatchValues).length = 3*xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [dispatchValues,Dispatch.metadataReads,ih,Nat.mul_succ]
  have steps (xs : List (Step F × F)) : (xs.flatMap stepValues).length = xs.length := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [stepValues,ih]
  rw [dispatches,steps,guardedRows_length,guardedRows_length]

end SP1Clean.WriteEffects.Witness.Metadata
