module

public import SP1Clean.Semantics.Host.HostExecution

/-! # Released WRITE routes and their ordered host effects

The two standard streams use full-width descriptor equality. The public, hint and seven hook
descriptors use the low 32 bits. Hooks consume the first supplied reply with the exact request,
including the entire ordered payload. The stdout and stderr streams record pre-rendering bytes.
-/

@[expose] public section

namespace SP1Clean.Semantics

/-- The endpoint selected by the released minimal executor. -/
inductive WriteRoute where
  | stdout | stderr | publicValues | hint | hook (descriptor : BitVec 32) | ignored
deriving DecidableEq, Repr

/-- The total released dispatch, including the default for every other descriptor. -/
def WriteRoute.ofDescriptor (fd : BitVec 64) : WriteRoute :=
  if fd = 1 then .stdout
  else if fd = 2 then .stderr
  else if fd.setWidth 32 = 13 then .publicValues
  else if fd.setWidth 32 = 14 then .hint
  else if fd.setWidth 32 ∈ hookDescriptors then .hook (fd.setWidth 32)
  else .ignored

/-- The route sent to the effect consumer. Zero denotes the default arm. -/
def WriteRoute.tag : WriteRoute → Nat
  | .stdout => 1
  | .stderr => 2
  | .publicValues => 13
  | .hint => 14
  | .hook fd => fd.toNat
  | .ignored => 0

/-- A single observed guest buffer and its entire host transition. -/
def WriteRoute.Effect (route : WriteRoute) (source : HostState) (bytes : Bytes) (target : HostState) : Prop :=
  match route with
  | .stdout => target = {source with stdout := source.stdout ++ bytes}
  | .stderr => target = {source with stderr := source.stderr ++ bytes}
  | .publicValues => target = {source with io.publicOutput := source.io.publicOutput ++ bytes}
  | .hint => target = {source with io.hints := bytes :: source.io.hints}
  | .hook fd =>
    let request : HookRequest := ⟨fd, bytes⟩
    ∃ hints rest, source.replies = ⟨request, hints⟩ :: rest ∧
      target = {source with
        io := {source.io with hints := hints ++ source.io.hints}
        replies := rest
        requests := source.requests ++ [request]}
  | .ignored => target = source

/-- The total descriptor classification and the executor induce exactly the same effects. -/
theorem WriteRoute.effect_iff (source target : HostState) (fd : BitVec 64) (bytes : Bytes) :
    (ofDescriptor fd).Effect source bytes target ↔ source.writeOutput fd bytes = some target := by
  unfold ofDescriptor HostState.writeOutput
  split_ifs <;> simp only [Effect, HostIO.writePublic, HostIO.writeHint, Option.some.injEq]
  all_goals try exact eq_comm
  constructor
  · rintro ⟨hints, rest, replies, rfl⟩
    simp [replies, HostIO.applyHook]
  · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq]
    rintro ⟨⟨io, rest⟩, ran, rfl⟩
    obtain ⟨hints, replies, rfl⟩ := (HostIO.applyHook_eq_some_iff ..).mp ran
    exact ⟨hints, rest, replies, rfl⟩

end SP1Clean.Semantics
