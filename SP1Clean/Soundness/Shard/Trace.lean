import SP1Clean.Soundness.HostObservedDynamic
import SP1Clean.Soundness.HostFinalMemoryExit
import SP1Clean.Soundness.HostFinalMemoryEncoding
import SP1Clean.FormalModel.ShardMachine

/-! # Raw acceptance of the exported native circuit as a Sail machine trace

`installed` is the complete-memory native assembly: the 25 instruction chips with HALT, ENTER,
COMMIT, COMMIT_DEFERRED, HINT_LEN and HINT_READ handlers, complete source authentication and the
target register/RAM validators, for one incoming snapshot, one supplied target snapshot and the
hint-queue verifier endpoint. Each of the 25 ordinary instruction chips publishes a gated receipt. The
supplied source and target fix the observation endpoints and the verifier checks their static Sail
frame. The exported circuit installs the verifier-owned commitment statement above it.
`sail_trace` turns raw acceptance of a public header into a trace of the PolyFun machine
`sp1Machine` from the complete incoming state. Each ordinary step of that machine is an official
Sail `try_step` that takes `Retire_Success` (`SailRetiresNormally`); each host step runs SP1's
concrete host interpreter on an ECALL of the committed program.

The accepted source boundary establishes image validity. `Endpoint` records the entire RAM map,
integer registers, clock and host projection. `DynamicMatch` identifies the five remaining mutable
Sail entries against the ordinary receipts in this same trace. The header binds the well-formed
commitment statement and every actual COMMIT/COMMIT_DEFERRED declaration agrees with it. Every
event in the trace belongs to the seven-call profile. Every ordinary source in this same trace
satisfies the released jump-link encoding and the native load/store span checks. Every active
source clock has phase one modulo eight.

The proof applies to every prime field with `2 ^ 25 < p`, including SP1's. All installed tables
are lookup-free, so projection preserves each row's constraints even when canonical prover data
changes. The exported host checker binds the decoded hint suffix and preserved host fields.
WRITE, VERIFY and the full resource-bounded compiler remain part of `SoundnessTarget` and
`CompilerTarget` (#12).
-/

namespace SP1Clean.Soundness.Shard

open Circuit Air.Flat Channels Machine Semantics FormalModel.Shard
open LeanRV64D (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The installed complete-memory native assembly for one incoming snapshot, one supplied target
snapshot (its memory and host bank) and the hint-queue verifier endpoint. -/
abbrev installed (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) : Ensemble (ZMod p) SP1PublicIO :=
  HostObserved.ensemble image source target final

/-- The complete installed registry includes the commitment declaration protocol. -/
theorem declarationsRegistered (image : ProgramImage) (source target : ExecutionSnapshot)
    (final : HostHintQueue.State (ZMod p)) :
    CommitmentDeclaration.channel.toRaw ∈ (installed image source target final).channels :=
  HostObserved.declarationsRegistered

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
  limbs : header.LimbBounds
  exit : header.exit_code.val = ((SP1StateBoundary.haltCode source target).getD 0).toNat

variable {image : ProgramImage} {source target : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)}

/-- What one accepted header proves: the checked source is valid and is the header's incoming
endpoint, the commitment statement is well formed, and the SP1 Sail machine has a trace from the
source whose ordinary writes respect ROM protection, whose declarations agree with the statement,
and whose ordinary history binds the supplied dynamic Sail bookkeeping, outgoing registers and RAM. -/
def SailTrace (commitments : CommitmentStatement) (image : ProgramImage)
    (source target : ExecutionSnapshot) (final : HostHintQueue.State (ZMod p))
    (header : SP1PublicIO (ZMod p)) : Prop :=
  ExecutionSourceValid image source ∧ header.SourceFor source ∧ SailBoundary.Spec source target header ∧
    CommitmentBoundary.Spec commitments header ∧
    ∃ (events : List ExecutionEvent) (actual : ExecutionState),
      (sp1Machine p image).Trace source.realize events actual ∧
      commitments.Matches events ∧ (∀ event ∈ events, HostReceiptProfile.event true event) ∧
      ExecutionPath.Encoded (policy p image) image.program source.realize events ∧
      ExecutionPath.ReleaseLinks (policy p image) image.program source.realize events ∧
      DynamicMatch source target events ∧ Endpoint source target final header events actual

/-- Constraints and balance outside the commitment declarations already give the trace; each
actual commitment call requests its declaration in the witness ledger. -/
theorem trace_of_witness
    (witness : EnsembleWitness (HostFinalMemory.Installed image source target final))
    (constraints : witness.Constraints) (balanced : HostFinalMemory.ExternallyBalanced witness) :
    ExecutionSourceValid image source ∧ witness.publicInput.SourceFor source ∧
      ∃ (events : List ExecutionEvent) (actual : ExecutionState),
        (sp1Machine p image).Trace source.realize events actual ∧
        Endpoint source target final witness.publicInput events actual ∧
        (∀ event ∈ events, HostReceiptProfile.event true event) ∧ HostFinalMemory.PhysicalEventOrder witness events ∧ CommitmentEnsemble.Declared witness events := by
  have ordering := HostHintQueueBoundary.projected_orderingChannels (HostFinalMemory.baseWitness witness)
    (GroundingResources.sourceInterface source.host.io.hints (FinalMemoryChecks.checkTables target.sail.memorySnapshot))
    (HostFinalMemory.baseWitness_constraints witness constraints)
    (HostFinalMemory.baseWitness_hostBalanced witness balanced)
  have contract := LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte
  have valid : image.Valid := contract.2.1.1.1
  rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput,
    HostFinalMemory.baseWitness_publicInput] at contract
  obtain ⟨events, actual, hints, path, clock, pc, registers, ram, runtime, nextPC,
    ⟨increment, retired⟩, ⟨interrupts, eventIndex⟩, preserved, decoded, host, exit, profile, order, declared⟩ :=
    HostFinalMemory.source_execution valid witness constraints balanced
  exact ⟨contract.2.1, contract.2.2.1, events, actual, trace_iff_executionPath.mpr (by rwa [image.program_eq valid]),
    { clock, pc, nextPC, increment, retired, interrupts, eventIndex, preserved, runtime, registers, ram
      host := ⟨hints, decoded, host⟩
      limbs := contract.1
      exit := HostFinalMemory.publicExit witness constraints balanced valid path order
        (by have status := congrArg HostState.exitCode host; exact status) exit }, profile, order, declared⟩

attribute [local irreducible] HostObserved.ensemble in
/-- **The exported native circuit proves a Sail trace.** Over any prime field with `2 ^ 25 < p`,
SP1's among them, raw acceptance of the complete-memory assembly with the verifier-owned
commitment statement installed above it gives a trace of the SP1 Sail machine from the valid
source snapshot, ending at the header's endpoint with the outgoing registers, RAM and dynamic Sail bookkeeping. The
statement's fixed provider authenticates every declaration request, so each actual
COMMIT/COMMIT_DEFERRED call agrees with the well-formed statement. The accepted source boundary
supplies image validity. Each ordinary replay cut satisfies the released link-write bound.
The header binds every public commitment field and each recovered
syscall decodes to one of the seven installed kinds. -/
theorem sail_trace {image : ProgramImage} {source target : ExecutionSnapshot}
    {final : HostHintQueue.State (ZMod p)}
    {commitments : CommitmentStatement}
    {fresh : (CommitmentDeclaration.source (p := p) commitments).circuit.name ∉
      (installed image source target final).tables.map (·.circuit.name)}
    {header : SP1PublicIO (ZMod p)} {heights : List ℕ}
    (accepted : (CommitmentEnsemble.install (p := p) commitments
      (installed image source target final) fresh
      (declarationsRegistered image source target final)).Statement .logUp header heights) :
    SailTrace commitments image source target final header := by
  have : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
  obtain ⟨fit, witness, rfl, rfl, constraints, rawBalance⟩ := accepted
  have balanced := EnsembleWitness.balancedChannels_of_balanced
    (witness.interactionsFit_of_heights fit) rawBalance
  let observed := CommitmentEnsemble.project witness
  have checked := CommitmentEnsemble.project_constraints witness HostObserved.lookupFree constraints
  have funded : HostObserved.DeclarationsOpen observed := fun channel member different =>
    CommitmentEnsemble.project_balancedChannel witness balanced channel member different
  have sail := HostObserved.target_spec observed funded
  obtain ⟨sourceValid, sourceFor, events, actual, trace, endpoint, profile, order, declared⟩ :=
    trace_of_witness (HostObserved.baseWitness observed) (HostObserved.baseWitness_constraints observed checked)
      (HostObserved.grounding_balance observed funded)
  have encoding := order.encoding (HostObserved.baseWitness observed) sourceValid.1.1
    (HostObserved.baseWitness_constraints observed checked) (HostObserved.grounding_balance observed funded)
  rw [← image.program_eq sourceValid.1.1] at encoding
  have silent := HostObserved.verifier_declarations_silent (image := image) (source := source)
    (target := target) (final := final)
  have requests : CommitmentEnsemble.Declared observed events := declared.transfer fun _ member => by
    rwa [HostObserved.baseWitness_declarations] at member
  have agrees := (requests.transfer fun _ member =>
    CommitmentEnsemble.project_declaration_mem witness silent member).agrees commitments
      (CommitmentEnsemble.declared_member witness
        (fun component member => HostObserved.declaration_sources _ component member)
        silent constraints balanced)
  rw [HostObserved.baseWitness_publicInput] at sourceFor endpoint
  exact ⟨sourceValid, sourceFor, sail, CommitmentEnsemble.statement_spec witness balanced, events, actual,
    trace, agrees, profile, encoding.1, encoding.2, HostObserved.dynamicMatch observed checked funded order, endpoint⟩

end SP1Clean.Soundness.Shard
