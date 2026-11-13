import Lean
import SP1Clean.Soundness.Shard.Machine
import SP1Clean.Soundness.Shard.Trace

/-! # Compiled native capstone contract audit

The examples pin the currently conditional target types, independently spelling out the raw
acceptance and complete-state interpretation. They do not instantiate the missing targets.
The command writes a dependency manifest to `CAPSTONE_SURFACE_OUT`: declaration types and
definition bodies are followed, but theorem proof bodies are not. External declarations form
the boundary supplied by the immutable dependency pins. Structural fingerprints detect drift;
they are not cryptographic commitments or a substitute for reviewing the definitions.

Run through `scripts/check_capstone_contract.py`, which builds the dependency first, checks
completion and diagnostics, and diffs the manifest. No main-library declaration is introduced.
-/

open SP1Clean SP1Clean.Model.Core SP1Clean.Machine SP1Clean.FormalModel.Shard
  SP1Clean.Soundness.Shard Air.Flat

section Contract

variable {p : ℕ} [Fact p.Prime]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
  (commitments : CommitmentStatement) (image : ProgramImage) (source target : ExecutionSnapshot) (header : PublicIO (ZMod p))

example (heights : List ℕ) : ensemble.Statement Balance.logUp header heights ↔
    ensemble.interactionsFit Balance.logUp heights ∧
    ∃ witness : EnsembleWitness ensemble,
      witness.publicInput = header ∧ witness.heights = heights ∧
        witness.Constraints ∧ witness.Balanced Balance.logUp := Iff.rfl

example : SoundnessTarget ensemble limits commitments image source target header =
    (∀ publicInput heights, True → ensemble.Statement Balance.logUp publicInput heights →
      ∃ events, publicInput = header ∧
        ((∃ valid : ExecutionSourceValid image source,
          ExecutionPath (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events target.realize) ∧ nativeProfile limits p image source target events) ∧
        commitments.WellFormed p ∧ commitments.Matches events) := rfl

example : CompilerTarget ensemble limits commitments image source target header =
    EnsembleCompiler ensemble Balance.logUp (List ExecutionEvent)
      (fun publicInput events => publicInput = header ∧
        ((∃ valid : ExecutionSourceValid image source,
          ExecutionPath (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events target.realize) ∧ nativeProfile limits p image source target events) ∧
        commitments.WellFormed p ∧ commitments.Matches events) := rfl

example (sound : SoundnessTarget ensemble limits commitments image source target header)
    (compiler : CompilerTarget ensemble limits commitments image source target header) :
    (∃ heights, ensemble.Statement Balance.logUp header heights) ↔ ∃ events, StatementExecution limits p commitments image source target events :=
  SP1Clean.Soundness.Shard.statement_iff sound compiler

end Contract

section NativeTraceContract

open SP1Clean.Soundness SP1Clean.Channels SP1Clean.Semantics

variable {image : ProgramImage} {source : ExecutionSnapshot} {outgoing : MemorySnapshot}
  {final : HostHintQueue.State (ZMod SP1Prime)} {bankFinal : HostState}
  {commitments : CommitmentStatement} {header : SP1PublicIO (ZMod SP1Prime)}

-- Pin the headline theorem's application surface independently of its proof.
example (valid : image.Valid)
    (fresh : (CommitmentDeclaration.source (p := SP1Prime) commitments).circuit.name ∉
      (installed image source outgoing final bankFinal).tables.map (·.circuit.name))
    (registered : CommitmentDeclaration.channel.toRaw ∈
      (installed image source outgoing final bankFinal).channels)
    (heights : List ℕ)
    (accepted : (CommitmentEnsemble.install commitments
      (installed image source outgoing final bankFinal) fresh registered).Statement .logUp header heights) :
    SailTrace commitments image valid source outgoing final bankFinal header :=
  sail_trace valid accepted

example (valid : image.Valid) :
    SailTrace commitments image valid source outgoing final bankFinal header ↔
      ExecutionSourceValid image source ∧ header.SourceFor source ∧ commitments.WellFormed SP1Prime ∧
        ∃ (events : List ExecutionEvent) (target : ExecutionState),
          (sp1Machine SP1Prime image valid).Trace source.realize events target ∧
          commitments.Matches events ∧
          Endpoint source outgoing final bankFinal header events target := Iff.rfl

-- These are complete boundary maps, not just values at accessed addresses.
example {events : List ExecutionEvent} {target : ExecutionState}
    (endpoint : Endpoint source outgoing final bankFinal header events target) :
    target.sail.mem = outgoing.memory.toSailMemory (2 ^ 48) ∧
      (∀ index, target.sail.get_reg? index = some (outgoing.read (.reg index))) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage header) :=
  ⟨endpoint.ram, endpoint.registers, endpoint.clock⟩

end NativeTraceContract

namespace CapstoneContractAudit

open Lean

/-- Exact declarations whose types/definitions determine the audited target and machine view. -/
def roots : Array Name := #[
  ``SP1Clean.Soundness.Shard.statement_iff,
  ``SP1Clean.Soundness.Shard.SoundnessTarget,
  ``SP1Clean.Soundness.Shard.CompilerTarget,
  ``SP1Clean.Soundness.Shard.SailTrace,
  ``SP1Clean.Soundness.Shard.Endpoint,
  ``SP1Clean.Soundness.Shard.sail_trace,
  ``SP1Clean.FormalModel.Shard.Executes,
  ``SP1Clean.FormalModel.Shard.nativeProfile,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution,
  ``SP1Clean.FormalModel.Shard.sp1Machine,
  ``Air.Flat.Realizes]

/-- The owning module is used rather than the namespace, which is decoupled from paths. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- Traverse repository definitions; pinned upstream declarations remain explicit boundary nodes. -/
def localModule (name : Name) : Bool :=
  ["SP1Clean", "ToClean", "ToMathlib"].any
    (fun rootName => name.toString.startsWith (rootName ++ "."))

/-- Theorem bodies are kernel-checked implementation, rather than definition dependencies. -/
def body? : ConstantInfo → Option Expr
  | .thmInfo _ => none
  | info => info.value? (allowOpaque := true)

/-- Iterative traversal retains types, constructors, instances and definition bodies. -/
def manifest (env : Environment) : Except String Json := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut entries : Array (String × Json) := #[]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw s!"missing declaration: {name}"
    let owner := moduleOf env name
    let repository := localModule owner
    let body := body? info
    entries := entries.push (name.toString, Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner.toString),
      ("local", toJson repository), ("typeFingerprint", toJson (toString (hash info.type))),
      ("bodyFingerprint", toJson (body.map (fun value => toString (hash value))))])
    if repository then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := body then
        pending := value.getUsedConstants.toList ++ pending
      if let .inductInfo declaration := info then
        pending := declaration.ctors ++ pending
  let sortedEntries := entries.qsort (fun left right => left.1 < right.1)
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("roots", toJson (roots.map Name.toString)),
    ("declarations", Json.arr (sortedEntries.map Prod.snd))]

run_cmd do
  let env ← Lean.getEnv
  let some destination ← IO.getEnv "CAPSTONE_SURFACE_OUT"
    | throwError "CAPSTONE_SURFACE_OUT is required; use scripts/check_capstone_contract.py"
  match manifest env with
  | .error message => throwError message
  | .ok result => IO.FS.writeFile destination (result.pretty ++ "\n")

end CapstoneContractAudit
