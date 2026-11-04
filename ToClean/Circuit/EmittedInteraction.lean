module

public import Clean.Circuit.Channel

/-! # Evaluated pushes with arbitrary multiplicity

Clean provides `Channel.emit` for counted pushes, while its evaluated-value helpers cover unit
and conditional pushes and pulls. `emittedValue` and its evaluation law complete the counted
push interface. Direction is explicit: consuming a message uses a pull, never a negative push.
These additions belong beside `Channel.pushedValue` in `Clean/Circuit/Channel.lean`.
-/

@[expose] public section

namespace Channel

variable {F : Type} [FiniteField F] {Message : TypeMap} [ProvableType Message]

@[circuit_norm]
def emittedValue (channel : Channel F Message) (mult : F) (msg : Message F) : Interaction F where
  channel := channel.toRaw
  mult := mult
  msg := (toElements msg).toArray
  same_size := by simp [Channel.toRaw]
  direction := .push

theorem eval_emitted {channel : Channel F Message} {mult : Expression F}
    {msg : Message (Expression F)} {env : Environment F} :
    (channel.emitted mult msg).toRaw.eval env = channel.emittedValue (env mult) (eval env msg) := by
  simp only [circuit_norm, AbstractInteraction.eval, Interaction.mk.injEq]
  simp only [true_and]
  congr
  rw [← ProvableType.fromElements_eq_iff, CircuitType.eval_var]
  rfl

end Channel
