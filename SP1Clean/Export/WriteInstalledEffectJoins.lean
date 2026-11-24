import SP1Clean.Export.WriteObserverSlotLedger
import SP1Clean.Proofs.Completeness.WriteEffectAssembly

/-! # Physical effect handoffs from the native WRITE collector -/

namespace SP1Clean.Export.WriteObservationAssembly

open Circuit Air.Flat Semantics WriteSourceRegistry WriteEffects.Witness
private abbrev F := ZMod SP1Prime

variable {image : ProgramImage} {source target : ExecutionSnapshot} {final : HostHintQueue.State F}

/-- Channels connecting the real buffer, request, word decoder, dispatcher and group table. -/
def effectProtocols : List (RawChannel F) :=
  [WriteBuffer.effectHeaderChannel.toRaw,WriteBuffer.wordChannel.toRaw,WriteEffects.requestChannel.toRaw,WriteEffects.octetsChannel.toRaw]

private theorem installed_effect_join (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (reg : suffix.map Table.component = tables source target) (ch : RawChannel F) (fresh : ch ∈ channels)
    (distinct : ch ≠ WriteProbe.readbackChannel.toRaw)
    (silent : ch.name ∉ [(WriteEffects.cursorChannel (p := SP1Prime)).name,(WriteEffects.closeChannel (p := SP1Prime)).name])
    (i j : Fin 19) (support : selectedSlots source target ch = [i,j]) (left right : Table F) {height : Nat}
    (atLeft : suffix[i.val]? = some left) (atRight : suffix[j.val]? = some right) (join : EffectJoin ch left right height) :
    let ledger := (withPublicChecks (build w suffix reg)).interactionsWith ch
    ledger.length = 2 * height ∧ LogUpBalanced ledger ∧ (Balance.logUp (F := F)).fits ledger.length = true ∧
      BalancedInteractions ledger := by
  dsimp only
  rw [build_pair_ledger w suffix reg ch fresh distinct silent i j support left right atLeft atRight]
  exact ⟨join.count,join.signed,join.fits,join.matched⟩

/-- All four exact-count joins survive the shared installation at their six actual registry
positions. The other thirteen tables may be constructed independently. -/
theorem installed_effect_joins (w : EnsembleWitness (base image source target final)) (suffix : List (Table F))
    (reg : suffix.map Table.component = tables source target) (spans words requests decoders dispatches groups : Table F)
    (callHeight wordHeight : Nat)
    (hs : suffix[3]? = some spans) (hw : suffix[4]? = some words) (hr : suffix[5]? = some requests)
    (ho : suffix[6]? = some decoders) (hd : suffix[8]? = some dispatches) (hg : suffix[9]? = some groups)
    (header : EffectJoin WriteBuffer.effectHeaderChannel.toRaw spans requests callHeight)
    (word : EffectJoin WriteBuffer.wordChannel.toRaw words decoders wordHeight)
    (request : EffectJoin WriteEffects.requestChannel.toRaw requests dispatches callHeight)
    (octets : EffectJoin WriteEffects.octetsChannel.toRaw decoders groups wordHeight) :
    ∀ (route : Fin 4), let ch := effectProtocols[route.val]'route.isLt
      let ledger := (withPublicChecks (build w suffix reg)).interactionsWith ch
      ledger.length = 2 * [callHeight,wordHeight,callHeight,wordHeight][route.val]'route.isLt ∧
        LogUpBalanced ledger ∧ (Balance.logUp (F := F)).fits ledger.length = true ∧ BalancedInteractions ledger := by
  intro route
  fin_cases route
  · exact installed_effect_join w suffix reg WriteBuffer.effectHeaderChannel.toRaw (by simp [channels]) (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 3 5 rfl _ _ hs hr header
  · exact installed_effect_join w suffix reg WriteBuffer.wordChannel.toRaw (by simp [channels]) (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 4 6 rfl _ _ hw ho word
  · exact installed_effect_join w suffix reg WriteEffects.requestChannel.toRaw (by simp [channels]) (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 5 8 rfl _ _ hr hd request
  · exact installed_effect_join w suffix reg WriteEffects.octetsChannel.toRaw (by simp [channels]) (by apply ne_of_apply_ne RawChannel.name; decide) (by decide) 6 9 rfl _ _ ho hg octets

end SP1Clean.Export.WriteObservationAssembly
