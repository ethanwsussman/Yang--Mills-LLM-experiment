import YangMills.Construction.ColdStepAtMirrorFrames.EmbeddedVariables
import YangMills.Construction.ColdStepAtMirrorFrames.OffsetsOfATorus
import YangMills.Construction.ColdStepAtMirrorFrames.PairedVariablesOfTwoTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
theorem pairedCoordinatesAgree_of_offsets (hoff : TorusOffsetsAboutCell) (hpush : PushforwardFieldProperties) :
    PairedCoordinatesAgree := by
  intro F F' Y Y' r ι _ _ j j' ξ h o i hside hodd hs hs' inj₁ inj₂ hm hh ho
  have hodd' : Odd F'.blockSide := hside ▸ hodd
  have ho' : o ∈ centredCube F'.blockSide := hside ▸ ho
  obtain ⟨c₁, u₁, _, k₁, _⟩ := hoff F r Y hodd hs
  obtain ⟨c₂, u₂, _, k₂, _⟩ := hoff F' r Y' hodd' hs'
  have hiff : fineBondAt Y h o i ∈ chordBonds (finiteCells F) ↔
      fineBondAt Y' h o i ∈ chordBonds (finiteCells F') := by
    have e₁ := k₁ (fineBondAt Y h o i).1 i
    have e₂ := k₂ (fineBondAt Y' h o i).1 i
    rw [(c₁ h o i ho).2] at e₁
    rw [(c₂ h o i ho').2] at e₂
    change fineBondAt Y h o i ∈ _ ↔ _ at e₁
    change fineBondAt Y' h o i ∈ _ ↔ _ at e₂
    rw [e₁, e₂, hside]
  refine ⟨hiff, ?_⟩
  obtain ⟨_, _, _, v₁, z₁, _⟩ := hpush _ _ _ inj₁
  obtain ⟨_, _, _, v₂, z₂, _⟩ := hpush _ _ _ inj₂
  by_cases hc : fineBondAt Y h o i ∈ chordBonds (finiteCells F)
  · have hc' := hiff.1 hc
    have d₁ : stepCoordinates (pushforwardField j ξ) (fineBondAt Y h o i).1 i =
        toImaginary (pushforwardField j ξ ⟨fineBondAt Y h o i, hc⟩) :=
      dif_pos (show ((fineBondAt Y h o i).1, i) ∈ chordBonds (finiteCells F) from hc)
    have d₂ : stepCoordinates (pushforwardField j' ξ) (fineBondAt Y' h o i).1 i =
        toImaginary (pushforwardField j' ξ ⟨fineBondAt Y' h o i, hc'⟩) :=
      dif_pos (show ((fineBondAt Y' h o i).1, i) ∈ chordBonds (finiteCells F') from hc')
    rw [d₁, d₂]
    congr 1
    by_cases hk : ∃ k, j k = ⟨fineBondAt Y h o i, hc⟩
    · obtain ⟨k, hk⟩ := hk
      obtain ⟨h₁, o₁, i₁, ho₁, hh₁, e₁, e₂⟩ := hm k
      have hk₁ : (j k).1 = fineBondAt Y h o i := congrArg Subtype.val hk
      have hi : i₁ = i := by
        have hsnd := congrArg Prod.snd (hk₁.symm.trans e₁)
        exact hsnd.symm
      subst hi
      obtain ⟨rfl, rfl⟩ := u₁ h h₁ o o₁ i₁ i₁ hh hh₁ ho ho₁ (congrArg Prod.fst (hk₁.symm.trans e₁))
      have hk₂ : j' k = ⟨fineBondAt Y' h o i₁, hc'⟩ := Subtype.ext e₂
      have t₁ := v₁ ξ k
      have t₂ := v₂ ξ k
      rw [← hk, ← hk₂]
      exact t₁.trans t₂.symm
    · have hk' : ∀ k, j' k ≠ ⟨fineBondAt Y' h o i, hc'⟩ := by
        intro k hek
        obtain ⟨h₁, o₁, i₁, ho₁, hh₁, e₁, e₂⟩ := hm k
        have hk₂ : (j' k).1 = fineBondAt Y' h o i := congrArg Subtype.val hek
        have hi : i₁ = i := by
          have hsnd := congrArg Prod.snd (hk₂.symm.trans e₂)
          exact hsnd.symm
        subst hi
        obtain ⟨rfl, rfl⟩ := u₂ h h₁ o o₁ i₁ i₁ hh hh₁ ho' (hside ▸ ho₁)
          (congrArg Prod.fst (hk₂.symm.trans e₂))
        exact hk ⟨k, Subtype.ext e₁⟩
      have hk₃ : ∀ k, j k ≠ ⟨fineBondAt Y h o i, hc⟩ := fun k hjk => hk ⟨k, hjk⟩
      rw [z₁ ξ ⟨fineBondAt Y h o i, hc⟩ hk₃, z₂ ξ ⟨fineBondAt Y' h o i, hc'⟩ hk']
  · have hc' : fineBondAt Y' h o i ∉ chordBonds (finiteCells F') := fun h' => hc (hiff.2 h')
    have t₁ : stepCoordinates (pushforwardField j ξ) (fineBondAt Y h o i).1 i = 0 :=
      dif_neg (show ¬ ((fineBondAt Y h o i).1, i) ∈ chordBonds (finiteCells F) from hc)
    have t₂ : stepCoordinates (pushforwardField j' ξ) (fineBondAt Y' h o i).1 i = 0 :=
      dif_neg (show ¬ ((fineBondAt Y' h o i).1, i) ∈ chordBonds (finiteCells F') from hc')
    rw [t₁, t₂]
end ColdStepAtMirrorFrames
end YangMills.Construction
end
