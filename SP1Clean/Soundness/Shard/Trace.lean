import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.HostFinalMemoryDeclarations
import SP1Clean.Soundness.CommitmentEnsemble
import SP1Clean.Soundness.HostFinalMemoryLookups
import SP1Clean.FormalModel.ShardMachine

/-! # Raw acceptance of the exported native circuit as a Sail machine trace

`installed` is the complete-memory native assembly: the 25 instruction chips with HALT, ENTER,
COMMIT, COMMIT_DEFERRED, HINT_LEN and HINT_READ handlers, complete source authentication and the
target register/RAM validators, for one incoming snapshot, one supplied target snapshot and the
hint-queue verifier endpoint. The exported circuit installs the verifier-owned commitment statement above it.
`sail_trace` turns raw acceptance of a public header into a trace of the PolyFun machine
`sp1Machine` from the complete incoming state. Each ordinary step of that machine is an official
Sail `try_step` that takes `Retire_Success` (`SailRetiresNormally`); each host step runs SP1's
concrete host interpreter on an ECALL of the committed program.

The statement has no caller-supplied grounding, provider validity, syscall inactivity or
readiness premise. `Endpoint` collects what the header and verifier endpoints fix about the
actual final state of that trace, including all integer registers and the entire RAM map. The
statement is well formed and every actual COMMIT/COMMIT_DEFERRED declaration agrees with it, as
`StatementExecution` requires. The theorem holds over every prime field with `2 ^ 25 < p`, SP1's
among them: every installed table is lookup-free, so forgetting the statement provider keeps
each row's constraints although canonical prover data changes at its name. Complete
outgoing-snapshot equality, WRITE/VERIFY installation and resource limits remain obligations of
`SoundnessTarget` (#12).
-/

namespace SP1Clean.Soundness.Shard

open Circuit Air.Flat Channels Machine Semantics FormalModel.Shard
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The installed complete-memory native assembly for one incoming snapshot, one supplied target
snapshot (its memory and host bank) and the hint-queue verifier endpoint. -/
abbrev installed (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) : Ensemble (ZMod p) SP1PublicIO :=
  HostFinalMemory.Installed image source target final

/-- The complete installed registry includes the commitment declaration protocol. -/
private theorem declarations_registered (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) :
    CommitmentDeclaration.channel.toRaw ∈ (installed image source target final).channels := by
  change _ ∈ (_ ++ [_]) ++ [_]
  apply List.mem_append_left _ (List.mem_append_left _ ?_)
  change _ ∈ _ ++ [_]
  apply List.mem_append_left
  simp [HostLocalCore.baseEnsemble, HostLocalCore.registry, HostFinalMemory.sourceChannels]

/-- What the public header and verifier endpoints fix about the final state of an accepted trace.
Retirement, interrupt refresh and event bookkeeping are exact functions of the trace,
including preservation of the initial values on empty or host-only segments. -/
structure Endpoint (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p))
    (header : SP1PublicIO (ZMod p)) (events : List ExecutionEvent) (actual : ExecutionState) : Prop where
  clock : actual.clock = StateMsg.timeNat (finalBoundaryStateMessage header)
  pc : actual.sail.regs.get? Register.PC = some (StateMsg.pcBits (finalBoundaryStateMessage header))
  nextPC : actual.sail.regs.get? Register.nextPC = nextPcAfter events
    (source.sail.registers.get? Register.nextPC) (some (StateMsg.pcBits (finalBoundaryStateMessage header)))
  increment : actual.sail.regs.get? Register.minstret_increment =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.minstret_increment
      else some (retirementEnabled source.sail.realize)
  retired : actual.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
    (fun value => value + BitVec.ofNat 64
      (if retirementEnabled source.sail.realize then events.countP ExecutionEvent.isOrdinary else 0))
  interrupts : actual.sail.regs.get? Register.mip =
    if events.countP ExecutionEvent.isOrdinary = 0 then source.sail.registers.get? Register.mip
      else some (TryStepReduction.refreshedMip source.sail.realize)
  eventIndex : actual.sail.regs.get? Register.written_event_index =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.written_event_index else some none
  preserved : ∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
    R ≠ Register.minstret_increment → R ≠ Register.mip → R ≠ Register.written_event_index → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
      actual.sail.regs.get? R = source.sail.registers.get? R
  runtime : actual.sail.cycleCount = source.sail.cycleCount ∧ actual.sail.sailOutput = source.sail.output
  registers : ∀ index, actual.sail.get_reg? index = some (target.sail.memorySnapshot.read (.reg index))
  ram : actual.sail.mem = target.sail.memorySnapshot.memory.toSailMemory (2 ^ 48)
  host : ∃ hints, HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
    actual.host = { source.host with
      io.hints := hints
      committed := target.host.committed
      deferred := target.host.deferred
      exitCode := target.host.exitCode }
  exit : ∀ code : BitVec 32, source.host.exitCode = none → actual.host.exitCode = some code →
    code.toNat = header.exit_code.val

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}

/-- What one accepted header proves: the checked source is valid and is the header's incoming
endpoint, the commitment statement is well formed, and the SP1 Sail machine has a trace from the
source whose ordinary writes respect ROM protection, whose declarations agree with the statement,
and whose final state has the header's endpoint and the outgoing registers and RAM. -/
def SailTrace (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p))
    (header : SP1PublicIO (ZMod p)) : Prop :=
  ExecutionSourceValid image source ∧ header.SourceFor source ∧ commitments.WellFormed p ∧
    ∃ (events : List ExecutionEvent) (actual : ExecutionState),
      (sp1Machine p image).Trace source.realize events actual ∧
      commitments.Matches events ∧
      Endpoint source target final header events actual

/-- Constraints and balance outside the commitment declarations already give the trace; each
actual commitment call requests its declaration in the witness ledger. -/
theorem trace_of_witness (valid : image.Valid)
    (witness : EnsembleWitness (installed image source target final))
    (constraints : witness.Constraints) (balanced : HostFinalMemory.DeclarationsOpen witness) :
    ExecutionSourceValid image source ∧ witness.publicInput.SourceFor source ∧
      ∃ (events : List ExecutionEvent) (actual : ExecutionState),
        (sp1Machine p image).Trace source.realize events actual ∧
        Endpoint source target final witness.publicInput events actual ∧
        CommitmentEnsemble.Declared witness events := by
  have ordering := HostHintQueueBoundary.projected_orderingChannels (HostFinalMemory.baseWitness witness)
    (HostFinalMemory.sourceInterface source.host.io.hints target.sail.memorySnapshot)
    (HostFinalMemory.baseWitness_constraints witness constraints)
    (HostFinalMemory.baseWitness_hostBalanced witness balanced)
  have contract := LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte
  rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput,
    HostFinalMemory.baseWitness_publicInput] at contract
  obtain ⟨events, actual, hints, path, clock, pc, registers, ram, runtime, nextPC,
    ⟨increment, retired⟩, ⟨interrupts, eventIndex⟩, preserved, decoded, host, exit, declared⟩ :=
    HostFinalMemory.source_execution valid witness constraints balanced
  exact ⟨contract.2.1, contract.2.2.1, events, actual, trace_iff_executionPath.mpr (by rwa [image.program_eq valid]),
    { clock, pc, nextPC, increment, retired, interrupts, eventIndex, preserved, runtime, registers, ram
      host := ⟨hints, decoded, host⟩
      exit }, declared⟩

/-- **The exported native circuit proves a Sail trace.** Over any prime field with `2 ^ 25 < p`,
SP1's among them, raw acceptance of the complete-memory assembly with the verifier-owned
commitment statement installed above it gives a trace of the SP1 Sail machine from the valid
source snapshot, ending at the header's endpoint with the outgoing registers and RAM. The
statement's fixed provider authenticates every declaration request, so each actual
COMMIT/COMMIT_DEFERRED call agrees with the well-formed statement. There is no premise beyond the
checked program image. -/
theorem sail_trace {image : ProgramImage} {source target : ExecutionSnapshot}
    {final : HostHintQueue.State (ZMod p)}
    (valid : image.Valid)
    {commitments : CommitmentStatement}
    {fresh : (CommitmentDeclaration.source (p := p) commitments).circuit.name ∉
      (installed image source target final).tables.map (·.circuit.name)}
    {header : SP1PublicIO (ZMod p)} {heights : List ℕ}
    (accepted : (CommitmentEnsemble.install commitments
      (installed image source target final) fresh
      (declarations_registered image source target final)).Statement .logUp header heights) :
    SailTrace commitments image source target final header := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  obtain ⟨fit, witness, rfl, rfl, constraints, rawBalance⟩ := accepted
  have balanced := EnsembleWitness.balancedChannels_of_balanced
    (witness.interactionsFit_of_heights fit) rawBalance
  obtain ⟨sourceValid, sourceFor, events, actual, trace, endpoint, declared⟩ :=
    trace_of_witness valid (CommitmentEnsemble.project witness)
      (CommitmentEnsemble.project_constraints witness HostFinalMemory.installed_lookupFree
        constraints)
      (fun channel member different =>
        CommitmentEnsemble.project_balancedChannel witness balanced channel member different)
  have silent := HostFinalMemory.verifier_declarations_silent (image := image) (source := source)
    (target := target) (final := final)
  have agrees := (declared.transfer fun _ member =>
    CommitmentEnsemble.project_declaration_mem witness silent member).agrees commitments
      (CommitmentEnsemble.declared_member witness
        (fun component member => HostFinalMemory.declaration_sources _ component member)
        silent constraints balanced)
  rw [CommitmentEnsemble.project_publicInput] at sourceFor endpoint
  exact ⟨sourceValid, sourceFor, (CommitmentEnsemble.statement_spec witness balanced).1, events, actual,
    trace, agrees, endpoint⟩

end SP1Clean.Soundness.Shard
