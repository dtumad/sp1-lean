module

public import SP1Clean.Semantics.Host.HintQueue

/-! # Decoding an ordered suffix of the canonical incoming hint store -/

@[expose] public section

namespace SP1Clean.Semantics.HintQueue

/-- In the canonical incoming store the newest node is numbered by the queue length. -/
theorem ofList_head (hints : List Bytes) : (ofList hints).2 = hints.length := by
  cases hints with
  | nil => rfl
  | cons bytes rest =>
    change (ofList rest).1.size + 1 = rest.length + 1
    rw [ofList_size]

/-- Terminal authentication at the suffix length recovers its complete ordered contents. -/
theorem decode_suffix (consumed suffix : List Bytes) :
    decode? (ofList (consumed ++ suffix)).1 suffix.length = some suffix := by
  have extension : Extends (ofList suffix).1 (ofList (consumed ++ suffix)).1 := by
    induction consumed with
    | nil => exact Extends.refl _
    | cons bytes rest ih => exact ih.trans (extends_push _ _)
  have suffixAt := (ofList_represents suffix).extend extension
  rw [ofList_head] at suffixAt
  exact decode?_of_represents suffixAt

end SP1Clean.Semantics.HintQueue
