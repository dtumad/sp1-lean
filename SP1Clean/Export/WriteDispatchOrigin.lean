import SP1Clean.Export.WriteGuestOctets
import SP1Clean.Export.WritePlacementWalks
import SP1Clean.Export.WriteWordOwner
import SP1Clean.Proofs.Operations.WriteRequestRows
import SP1Clean.Proofs.Chips.WritePacket.Physical

/-! # Full chronological dispatcher headers from genuine WRITE ECALLs -/

namespace SP1Clean.Export.WriteObservationAssembly
open Circuit Air.Flat Semantics Soundness WriteEffects WriteSourceRegistry
private abbrev F := ZMod SP1Prime
attribute [local instance 2000] FiniteField.instDecidableEq
variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}
private abbrev original (w : EnsembleWitness (preprocessing image source target final)) :
    EnsembleWitness (HostObserved.ensemble image source target final) := supervisor w

attribute [local irreducible] withSources preprocessing

/-- All active physical WRITE packet instructions, including zero-length writes. -/
def physicalPackets (w : EnsembleWitness (preprocessing image source target final)) : List (WritePacket.Inputs F) :=
  enabledInputs (guardedInputs WritePacket.Inputs ((packetSlot image source target final).table w))

/-- Genuine packet headers and actual dispatcher headers match as lists up to permutation.
The span and classifier both preserve the full instruction header. The classifier also
establishes the released descriptor route for every dispatcher occurrence. -/
theorem native_dispatch_headers (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) :
    ((physicalPackets (observed w)).map WritePacket.Inputs.header).Perm
      ((physicalDispatches (observed w)).map fun d => d.request.header) ∧
    ∀ d ∈ physicalDispatches (observed w), d.request.Valid ∧ ∃ span : WriteBuffer.Span F, span.Valid ∧ span.header = d.request.header := by
  let seen := observed w
  let p := packetSlot image source target final
  let s := slot image source target final 3
  let c := slot image source target final 5
  have checks := (observed_constraints w).mp ok
  have pv := guarded_table_facts (I := WritePacket.Inputs) (t := p.table seen) (P := WritePacket.Spec) (by
    intro row m
    have valid := p.table_constraints seen checks row m
    rw [p.table_component seen] at valid
    exact WritePacket.packet_valid_at _ valid)
  have sv := guarded_table_facts (I := WriteBuffer.Span) (t := s.table seen) (P := WriteBuffer.Span.Valid) (by
    intro row m
    have valid := s.table_constraints seen checks row m
    have bytes := (byte_guarantees seen checks (observed_byte_balance w fit raw)).2 _ (s.table_mem seen) row m
    rw [s.table_component seen] at valid bytes
    exact WriteBuffer.spanInput_valid _ valid bytes)
  have cv := guarded_table_facts (I := Request) (t := c.table seen) (P := Request.Valid) (by
    intro row m
    have valid := c.table_constraints seen checks row m
    rw [c.table_component seen] at valid
    exact request_valid_at _ valid)
  have rp : (WritePacket.channel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 2) rfl
  have re : (WriteBuffer.effectHeaderChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 4) rfl
  have rr : (requestChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 6) rfl
  have packets := guarded_slots_perm WritePacket.channel seen 2 3 rp
    (fun eq => Bool.noConfusion (congrArg (fun ch => ch.name == "sp1.native.write_readback") eq))
    rfl WritePacket.Inputs.header WriteBuffer.Span.header WritePacket.header_at WriteBuffer.span_input_at pv.1 sv.1
    (observed_balance w fit raw _ (protocol_installed image source target final _ rp) (of_decide_eq_true rfl))
  have headers := guarded_slots_perm WriteBuffer.effectHeaderChannel seen 3 5 re
    (fun eq => Bool.noConfusion (congrArg (fun ch => ch.name == "sp1.native.write_readback") eq))
    rfl WriteBuffer.Span.header Request.header WriteBuffer.span_output_at request_header_at sv.1 cv.1
    (observed_balance w fit raw _ (protocol_installed image source target final _ re) (of_decide_eq_true rfl))
  have requests := guarded_slots_perm requestChannel seen 5 8 rr
    (fun eq => Bool.noConfusion (congrArg (fun ch => ch.name == "sp1.native.write_readback") eq))
    rfl id Dispatch.request request_output_at dispatch_request_at cv.1 (fun r m => (native_dispatch_input_facts w ok fit raw r m).1)
    (observed_balance w fit raw _ (protocol_installed image source target final _ rr) (of_decide_eq_true rfl))
  rw [List.map_id_fun] at requests
  have eq := requests.map (fun r : Request F => r.header)
  rw [List.map_map] at eq
  have all := headers.trans eq
  refine ⟨packets.trans all,?_⟩
  intro d md
  obtain ⟨span,ms,h⟩ := List.mem_map.mp (all.mem_iff.mpr (List.mem_map_of_mem md))
  exact ⟨cv.2 _ (requests.mem_iff.mpr (List.mem_map_of_mem md)),span,sv.2 span ms,h⟩

private theorem packet_origin (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (p : WritePacket.Inputs F) (mp : p ∈ physicalPackets (observed w)) :
    let seen := observed w
    let host := WriteSourceRegistry.hostWitness (original seen)
    WritePacket.Spec p ∧ WriteProbe.ReadMeaning (rawSource ((appended image source target final).project seen)) p.read ∧
      ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable host) host.data, HostCallLedger.call env = p.call := by
  let seen := observed w
  let z := packetSlot image source target final
  have checks := (observed_constraints w).mp ok
  obtain ⟨x,kept,rfl⟩ := List.mem_map.mp mp
  obtain ⟨present,flag⟩ := List.mem_filter.mp kept
  obtain ⟨row,m,rfl⟩ := List.mem_map.mp present
  let env := (z.table seen).environment row
  let input := valueFromOffset WritePacket.Row 0 env
  have act : input.2 = 1 := of_decide_eq_true flag
  have localCheck := z.table_constraints seen checks row m
  rw [z.table_component seen] at localCheck
  refine ⟨(WritePacket.packet_valid_at env localCheck).2 act,?_,?_⟩
  · have reg : (WriteProbe.readChannel (p := SP1Prime)).toRaw ∈ channels := List.mem_of_getElem? (i := 1) rfl
    apply assembled_read_origin w ok fit raw
    rw [← observed_ledger w _ (protocol_installed image source target final _ reg) (of_decide_eq_true rfl)]
    apply z.table_interactions_subset
    apply List.mem_flatMap.mpr
    refine ⟨row,m,?_⟩
    change _ ∈ (z.table seen).component.operations.interactionValuesWith WriteProbe.readChannel.toRaw env
    rw [z.table_component seen,WritePacket.read_at]
    apply List.mem_singleton.mpr
    change WriteProbe.readChannel.pulledValue input.1.read = WriteProbe.readChannel.pulledIfValue input.2 input.1.read
    rw [act]; rfl
  · have paid := native_packet_balance w fit raw
    have all := eight_calls (original seen) (supervisor_constraints seen checks) (z.table seen) (z.table_component seen)
      (z.table_constraints seen checks) paid
    have received : input.1.call ∈ ReceiverView.tableMessages WritePacket.receiver (z.table seen) := by
      apply List.mem_map.mpr
      refine ⟨row,List.mem_filter.mpr ⟨m,decide_eq_true ?_⟩,?_⟩
      · change env (varFromOffset WritePacket.Row 0).2 = 1
        simpa only [Guarded.eval_activity,eval_varFromOffset_valueFromOffset] using act
      · change eval env (varFromOffset WritePacket.Row 0).1.call = input.1.call
        have projection (v : Var WritePacket.Row F) : eval env v.1.call = (eval env v).1.call := by
          simp only [WritePacket.Inputs.call,ClockParts.high24,ClockParts.low24,circuit_norm]
        rw [projection,eval_varFromOffset_valueFromOffset]
    exact List.mem_map.mp (all.mem_iff.mpr (List.mem_append_right _ received))

/-- CPU, x12, and full-descriptor origins of a single physical chronological dispatcher. -/
def DispatchOrigin (w : EnsembleWitness (assembly image source target final)) (d : Dispatch F) : Prop :=
    let seen := observed w
    let host := WriteSourceRegistry.hostWitness (original seen)
    d.request.Valid ∧ ∃ p ∈ physicalPackets seen, p.header = d.request.header ∧ WritePacket.Spec p ∧
      WriteProbe.ReadMeaning (rawSource ((appended image source target final).project seen)) p.read ∧
      ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable host) host.data, HostCallLedger.call env = p.call

/-- The dispatcher has an actual active original CPU WRITE call, the original x12
read at its incoming clock, and a route classified from its actual guest descriptor. -/
theorem native_dispatch_origin (w : EnsembleWitness (assembly image source target final)) (ok : w.Constraints)
    (fit : w.InteractionsFit .logUp) (raw : w.Balanced .logUp) (d : Dispatch F) (md : d ∈ physicalDispatches (observed w)) :
    DispatchOrigin w d := by
  obtain ⟨headers,checked⟩ := native_dispatch_headers w ok fit raw
  obtain ⟨p,mem,header⟩ := List.mem_map.mp (headers.mem_iff.mpr (List.mem_map_of_mem md))
  exact ⟨(checked d md).1,p,mem,header,packet_origin w ok fit raw p mem⟩

end SP1Clean.Export.WriteObservationAssembly
