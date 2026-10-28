import SP1Clean.Soundness.HostFinalMemoryExecution
import SP1Clean.Soundness.CommitmentEnsemble
import SP1Clean.FormalModel.ShardMachine

/-! # Raw acceptance of the installed native assembly as a Sail machine trace

`installed` is the complete-memory native assembly: the 25 instruction chips with HALT, ENTER,
COMMIT, COMMIT_DEFERRED, HINT_LEN and HINT_READ handlers, complete source authentication and the
target register/RAM validators, for one incoming snapshot, outgoing memory snapshot and verifier
endpoint. `trace_of_statement` turns raw acceptance of a public header into a trace of the PolyFun
machine `sp1Machine` from the complete incoming state. Each ordinary step of that machine is an
official Sail `try_step` that takes `Retire_Success` (`SailRetiresNormally`); each host step runs
SP1's concrete host interpreter on an ECALL committed in both the program and Sail memory.

The statement has no caller-supplied grounding, provider validity, syscall inactivity or
readiness premise. `Endpoint` collects what the header and verifier endpoints fix about the
actual final state of that trace, including all integer registers and the entire RAM map.
`trace_of_committed_statement` covers the assembly with the verifier-owned commitment statement
installed, including COMMIT/COMMIT_DEFERRED calls; the bare assembly has no declaration provider
and accepts no active commitment call. Agreement of the declarations with the immutable statement,
complete outgoing-snapshot equality, WRITE/VERIFY installation and resource limits remain
obligations of `SoundnessTarget` (#12).
-/

namespace SP1Clean.Soundness.Shard

open Circuit Air.Flat Channels Machine Model.Core Semantics FormalModel.Shard
open LeanRV64D.Defs (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The installed complete-memory native assembly for one incoming snapshot, outgoing memory
snapshot and verifier endpoint. -/
abbrev installed (image : ProgramImage) (source : ExecutionSnapshot) (outgoing : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (channels : List (RawChannel (ZMod p))) : Ensemble (ZMod p) SP1PublicIO :=
  HostFinalMemory.Installed image source outgoing final bankFinal channels

/-- What the public header and verifier endpoints fix about the final state of an accepted trace.
The retirement bookkeeping is the exact function of the trace that official Sail computes. -/
structure Endpoint (source : ExecutionSnapshot) (outgoing : MemorySnapshot)
    (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState) (header : SP1PublicIO (ZMod p))
    (events : List ExecutionEvent) (target : ExecutionState) : Prop where
  clock : target.clock = StateMsg.timeNat (finalBoundaryStateMessage header)
  pc : target.sail.regs.get? Register.PC = some (StateMsg.pcBits (finalBoundaryStateMessage header))
  nextPC : target.sail.regs.get? Register.nextPC = nextPcAfter events
    (source.sail.registers.get? Register.nextPC) (some (StateMsg.pcBits (finalBoundaryStateMessage header)))
  increment : target.sail.regs.get? Register.minstret_increment =
    if events.countP ExecutionEvent.isOrdinary = 0
      then source.sail.registers.get? Register.minstret_increment
      else some (retirementEnabled source.sail.realize)
  retired : target.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
    (fun value => value + BitVec.ofNat 64
      (if retirementEnabled source.sail.realize then events.countP ExecutionEvent.isOrdinary else 0))
  preserved : ∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
    R ≠ Register.minstret_increment → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
      target.sail.regs.get? R = source.sail.registers.get? R
  runtime : target.sail.cycleCount = source.sail.cycleCount ∧ target.sail.sailOutput = source.sail.output
  registers : ∀ index, target.sail.get_reg? index = some (outgoing.read (.reg index))
  ram : target.sail.mem = outgoing.memory.toSailMemory (2 ^ 48)
  host : ∃ hints, HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
    target.host = { source.host with
      io.hints := hints
      committed := bankFinal.committed
      deferred := bankFinal.deferred
      exitCode := bankFinal.exitCode }
  exit : ∀ code : BitVec 32, source.host.exitCode = none → target.host.exitCode = some code →
    code.toNat = header.exit_code.val

variable {image : ProgramImage} {source : ExecutionSnapshot} {outgoing : MemorySnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- What one accepted header proves: the checked source is valid and is the header's incoming
endpoint, and the SP1 Sail machine has a trace from it whose ordinary writes respect ROM
protection and whose final state has the header's endpoint and the outgoing registers and RAM. -/
def SailTrace (image : ProgramImage) (valid : image.Valid) (source : ExecutionSnapshot)
    (outgoing : MemorySnapshot) (final : HostHintQueue.State (ZMod p)) (bankFinal : HostState)
    (header : SP1PublicIO (ZMod p)) : Prop :=
  ExecutionSourceValid image source ∧ header.SourceFor source ∧
    ∃ (events : List ExecutionEvent) (target : ExecutionState),
      (sp1Machine p image valid).Trace source.realize events target ∧
      ExecutionPath.WritesPermitted (policy p image) (image.toGuestProgram valid) source.realize events ∧
      Endpoint source outgoing final bankFinal header events target

/-- Constraints and balance outside the commitment declarations already give the trace. -/
theorem trace_of_witness (valid : image.Valid)
    (witness : EnsembleWitness (installed image source outgoing final bankFinal channels))
    (constraints : witness.Constraints) (balanced : HostFinalMemory.DeclarationsOpen witness) :
    SailTrace image valid source outgoing final bankFinal witness.publicInput := by
  have ordering := HostHintQueueBoundary.projected_orderingChannels (HostFinalMemory.baseWitness witness)
    (HostFinalMemory.sourceInterface source.host.io.hints outgoing)
    (HostFinalMemory.baseWitness_constraints witness constraints)
    (HostFinalMemory.baseWitness_hostBalanced witness balanced)
  have contract := LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte
  rw [HostLocalCore.localWitness_publicInput, HostHintQueueBoundary.projected_publicInput,
    HostFinalMemory.baseWitness_publicInput] at contract
  obtain ⟨events, target, hints, path, permitted, clock, pc, registers, ram, runtime, nextPC,
    ⟨increment, retired⟩, preserved, decoded, host, exit⟩ :=
    HostFinalMemory.source_execution valid witness constraints balanced
  exact ⟨contract.2.1, contract.2.2.1, events, target, trace_iff_executionPath.mpr path, permitted,
    { clock, pc, nextPC, increment, retired, preserved, runtime, registers, ram
      host := ⟨hints, decoded, host⟩
      exit }⟩

/-- **Native soundness as a Sail trace.** Raw acceptance of the complete-memory assembly. Without
a declaration provider this assembly accepts no active COMMIT/COMMIT_DEFERRED call. -/
theorem trace_of_statement (valid : image.Valid) {header : SP1PublicIO (ZMod p)}
    (accepted : (installed image source outgoing final bankFinal channels).Statement header) :
    SailTrace image valid source outgoing final bankFinal header := by
  obtain ⟨witness, rfl, constraints, balanced⟩ := accepted
  exact trace_of_witness valid witness constraints (.of_balancedChannels balanced)

/-- **Native soundness as a Sail trace, with the commitment statement.** Raw acceptance of the
complete-memory assembly with the verifier-owned commitment statement installed above it, which
admits COMMIT and COMMIT_DEFERRED calls. `lookupFree` is a static fact about the installed
circuits, never about a witness: it lets the provider be forgotten although canonical prover
data changes at its name. -/
theorem trace_of_committed_statement (valid : image.Valid) {commitments : CommitmentStatement}
    {fresh : (CommitmentDeclaration.source (p := p) commitments).circuit.name ∉
      (installed image source outgoing final bankFinal channels).tables.map (·.circuit.name)}
    (lookupFree : ∀ component ∈ (installed image source outgoing final bankFinal channels).tables,
      component.operations.lookups = [])
    {header : SP1PublicIO (ZMod p)}
    (accepted : (CommitmentEnsemble.install commitments
      (installed image source outgoing final bankFinal channels) fresh).Statement header) :
    SailTrace image valid source outgoing final bankFinal header := by
  obtain ⟨witness, rfl, constraints, balanced⟩ := accepted
  rw [← CommitmentEnsemble.project_publicInput witness]
  exact trace_of_witness valid (CommitmentEnsemble.project witness)
    (CommitmentEnsemble.project_constraints witness lookupFree constraints)
    (fun channel member different =>
      CommitmentEnsemble.project_balancedChannel witness balanced channel member different)

end SP1Clean.Soundness.Shard
