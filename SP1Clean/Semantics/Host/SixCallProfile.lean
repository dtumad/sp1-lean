module

public import SP1Clean.Semantics.Execution.EventExecution
public import SP1Clean.Semantics.ISA.SyscallCode

/-! # Event vocabulary of the six installed host handlers

The profile classifies the full syscall register word of an event. Ordinary instructions
belong to every host profile. Execution and the effects of calls use the shared machine
transition.
-/

@[expose] public section

namespace SP1Clean.Semantics.SixCallProfile

/-- The syscall kinds handled by the six-call assembly. -/
def kinds : List SyscallKind :=
  [.halt, .enterUnconstrained, .commit, .commitDeferred, .hintLength, .hintRead]

/-- The canonical full-word decoder selects a member of the installed profile. -/
def code (word : BitVec 64) : Prop :=
  ∃ kind ∈ kinds, SyscallKind.decode? word = some kind

/-- Each ordinary event is admitted, and each syscall carries its complete installed code. -/
def event : Machine.ExecutionEvent → Prop
  | .ordinary => True
  | .syscall call => code call.rawCode

/-- The full-word decoder makes the selected handler unique. -/
theorem code_iff_unique (word : BitVec 64) :
    code word ↔ ∃! kind, kind ∈ kinds ∧ SyscallKind.decode? word = some kind := by
  constructor
  · rintro ⟨kind, member, decoded⟩
    exact ⟨kind, ⟨member, decoded⟩, fun _ other => Option.some.inj (other.2.symm.trans decoded)⟩
  · rintro ⟨kind, ⟨member, decoded⟩, _⟩
    exact ⟨kind, member, decoded⟩

/-- WRITE's canonical code lies outside the six-handler inventory. -/
theorem ne_write {word : BitVec 64} (admitted : code word) : word ≠ SyscallKind.write.code := by
  obtain ⟨kind, member, decoded⟩ := admitted
  intro same
  have eq := SyscallKind.code_injective ((SyscallKind.decode?_eq_some_iff _ _).mp decoded |>.trans same)
  subst kind
  exact (by decide : SyscallKind.write ∉ kinds) member

end SP1Clean.Semantics.SixCallProfile

namespace SP1Clean.Semantics.HostReceiptProfile

/-- Full words admitted by the receiver inventory. The extended no-effect slot also accepts VERIFY. -/
def code : Bool → BitVec 64 → Prop
  | false => SixCallProfile.code
  | true => fun word => SixCallProfile.code word ∨ word = SyscallKind.verifyProof.code

/-- Both configurations retain all six original host calls. -/
theorem of_six (includeVerify : Bool) {word : BitVec 64} (admitted : SixCallProfile.code word) :
    code includeVerify word := by
  cases includeVerify
  · exact admitted
  · exact Or.inl admitted

end SP1Clean.Semantics.HostReceiptProfile
