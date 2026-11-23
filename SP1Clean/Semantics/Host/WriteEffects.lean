module

public import SP1Clean.Semantics.Host.WriteDescriptor
public import SP1Clean.Semantics.Host.HintQueue

/-! # Endpoint-owned WRITE streams and consumed hook replies

The source and target determine each appended byte and the entire prefix of consumed replies.
The first stream byte and first hook request use position zero within the local segment, even
when the incoming snapshot already contains output. Direct hints can be consumed within the
same segment, so their contents must come from the chronological guest buffers.
-/

@[expose] public section

namespace SP1Clean.Semantics

/-- Ordered local changes to the append-only streams and the incoming hook reply queue. -/
structure WriteStreams where
  stdout : Bytes := []
  stderr : Bytes := []
  publicOutput : Bytes := []
  hooks : List HookReply := []
deriving DecidableEq, Repr, Inhabited

namespace WriteStreams

/-- The verifier recovers the local stream slices from its two public snapshots. -/
def fromEndpoints (source target : HostState) : WriteStreams where
  stdout := target.stdout.drop source.stdout.length
  stderr := target.stderr.drop source.stderr.length
  publicOutput := target.io.publicOutput.drop source.io.publicOutput.length
  hooks := source.replies.take (source.replies.length - target.replies.length)

/-- Includes every submitted request and its corresponding supplied reply, in call order. -/
structure Binds (trace : WriteStreams) (source target : HostState) : Prop where
  stdout : target.stdout = source.stdout ++ trace.stdout
  stderr : target.stderr = source.stderr ++ trace.stderr
  publicOutput : target.io.publicOutput = source.io.publicOutput ++ trace.publicOutput
  replies : source.replies = trace.hooks ++ target.replies
  requests : target.requests = source.requests ++ trace.hooks.map HookReply.request

/-- Exact fixed-snapshot check. Every dynamic row must additionally bind its position and bytes. -/
def check (source target : HostState) : Bool :=
  let trace := fromEndpoints source target
  target.stdout == source.stdout ++ trace.stdout &&
    target.stderr == source.stderr ++ trace.stderr &&
    target.io.publicOutput == source.io.publicOutput ++ trace.publicOutput &&
    source.replies == trace.hooks ++ target.replies &&
    target.requests == source.requests ++ trace.hooks.map HookReply.request

theorem check_iff (source target : HostState) :
    check source target = true ↔ (fromEndpoints source target).Binds source target := by
  simp only [check, Bool.and_eq_true, beq_iff_eq]
  exact ⟨fun ⟨⟨⟨⟨o,e⟩,p⟩,r⟩,q⟩ => ⟨o,e,p,r,q⟩, fun h => ⟨⟨⟨⟨h.stdout,h.stderr⟩,h.publicOutput⟩,h.replies⟩,h.requests⟩⟩

/-- A locally authenticated itinerary of output effects is exactly the verifier-owned streams. -/
theorem Binds.unique {trace : WriteStreams} {source target : HostState} (h : trace.Binds source target) :
    fromEndpoints source target = trace := by
  cases trace
  simp only [fromEndpoints, h.stdout, h.stderr, h.publicOutput, h.replies, List.drop_left,
    List.length_append, Nat.add_sub_cancel_right, List.take_left]

/-- Chronological concatenation keeps each stream's byte order and consumes replies from the front. -/
def append (first last : WriteStreams) : WriteStreams :=
  ⟨first.stdout ++ last.stdout, first.stderr ++ last.stderr, first.publicOutput ++ last.publicOutput, first.hooks ++ last.hooks⟩

theorem Binds.append {first last : WriteStreams} {source middle target : HostState}
    (a : first.Binds source middle) (b : last.Binds middle target) :
    (first.append last).Binds source target := by
  constructor
  · simp only [WriteStreams.append, b.stdout, a.stdout, List.append_assoc]
  · simp only [WriteStreams.append, b.stderr, a.stderr, List.append_assoc]
  · simp only [WriteStreams.append, b.publicOutput, a.publicOutput, List.append_assoc]
  · rw [a.replies, b.replies]; simp [WriteStreams.append]
  · simp only [WriteStreams.append, b.requests, a.requests, List.map_append, List.append_assoc]

/-- The actual output and reply changes for one event. The chosen reply's returned hints are
retained even when the guest consumes them before the terminal snapshot. -/
def ofEvent (route : WriteRoute) (source : HostState) (bytes : Bytes) : WriteStreams :=
  match route with
  | .stdout => {stdout := bytes}
  | .stderr => {stderr := bytes}
  | .publicValues => {publicOutput := bytes}
  | .hook _ => {hooks := source.replies.take 1}
  | .hint | .ignored => {}

theorem ofEvent_binds {route : WriteRoute} {source target : HostState} {bytes : Bytes}
    (effect : route.Effect source bytes target) : (ofEvent route source bytes).Binds source target := by
  cases route <;> simp only [WriteRoute.Effect] at effect
  case hook fd =>
    obtain ⟨hints, rest, replies, rfl⟩ := effect
    constructor <;> simp [ofEvent, replies]
  all_goals subst target; constructor <;> simp [ofEvent]

end WriteStreams
end SP1Clean.Semantics
