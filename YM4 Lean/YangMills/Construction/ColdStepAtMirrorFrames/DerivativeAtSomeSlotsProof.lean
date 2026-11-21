import YangMills.Construction.ColdStepAtMirrorFrames.DerivativeAtSomeSlots
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace SlotEmbedding
variable {F : BlockFrame}
def slotEmbedding {m k : ℕ} (ι : Fin m → Fin k) : (Fin m → ℝ) →L[ℝ] (Fin k → ℝ) :=
  ∑ l, (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin m => ℝ) l).smulRight
    (Pi.single (ι l) (1 : ℝ))
theorem slotEmbedding_apply {m k : ℕ} (ι : Fin m → Fin k) (σ : Fin m → ℝ) (l' : Fin k) :
    slotEmbedding ι σ l' = ∑ l, if ι l = l' then σ l else 0 := by
  classical
  simp only [slotEmbedding, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun l _ => ?_
  by_cases h : ι l = l'
  · subst h; simp
  · simp [h, Pi.single_apply, Ne.symm h]
theorem slotEmbedding_single {m k : ℕ} (ι : Fin m → Fin k) (hι : Function.Injective ι) (l : Fin m) :
    slotEmbedding ι (Pi.single l 1) = Pi.single (ι l) 1 := by
  classical
  funext l'
  rw [slotEmbedding_apply]
  by_cases h : ι l = l'
  · subst h
    simp only [Pi.single_eq_same]
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb
      have : ι b ≠ ι l := fun e => hb (hι e)
      simp [this]
    · simp
  · rw [Pi.single_eq_of_ne (Ne.symm h)]
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : ι b = l'
    · have : b ≠ l := fun e => h (e ▸ hb)
      simp [hb, Pi.single_eq_of_ne this]
    · simp [hb]
theorem bondSpread_slotEmbedding {j m k : ℕ} (c : Fin k → F.Site j × Fin 4)
    (X : Fin k → imaginaryQuaternions) (ι : Fin m → Fin k)
    (σ : Fin m → ℝ) (hι : Function.Injective ι) :
    bondSpread c X (slotEmbedding ι σ) = bondSpread (c ∘ ι) (X ∘ ι) σ := by
  classical
  funext y i
  unfold bondSpread
  have : ∀ l' : Fin k, (if c l' = (y, i) then slotEmbedding ι σ l' • X l' else 0) =
      ∑ l, if ι l = l' then (if c (ι l) = (y, i) then σ l • X (ι l) else 0) else 0 := by
    intro l'
    rw [slotEmbedding_apply]
    by_cases h : c l' = (y, i)
    · rw [if_pos h, Finset.sum_smul]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases e : ι l = l'
      · subst e; simp [h]
      · simp [e]
    · rw [if_neg h]
      symm
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases e : ι l = l'
      · subst e; simp [h]
      · simp [e]
  simp_rw [this]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp
end SlotEmbedding
open SlotEmbedding
theorem iteratedDerivSubsetSlots_holds : IteratedDerivSubsetSlots := by
  intro E _ _ F j k m G W c X ι hι hc
  set g : (Fin k → ℝ) → E := fun τ => G (leftTranslate (bondSpread c X τ) W) with hg
  have hcomp : (fun σ : Fin m → ℝ => G (leftTranslate (bondSpread (c ∘ ι) (X ∘ ι) σ) W)) =
      g ∘ slotEmbedding ι := by
    funext σ
    simp only [hg, Function.comp_apply, bondSpread_slotEmbedding c X ι σ hι]
  unfold bondDeriv
  rw [hcomp]
  obtain ⟨u, hu, hon⟩ := hc.contDiffOn (m := m) le_rfl (by simp)
  obtain ⟨v, hvu, hvo, h0⟩ := mem_nhds_iff.1 hu
  have hS : ContDiffOn ℝ m g v := hon.mono (fun x hx => by simpa using hvu hx)
  have hs : UniqueDiffOn ℝ v := hvo.uniqueDiffOn
  have hs' : IsOpen ((slotEmbedding ι) ⁻¹' v) := hvo.preimage (slotEmbedding ι).continuous
  have h0' : (slotEmbedding ι) 0 ∈ v := by simpa using h0
  have key := (slotEmbedding ι).iteratedFDerivWithin_comp_right hS hs hs'.uniqueDiffOn h0' le_rfl
  rw [iteratedFDerivWithin_of_isOpen _ hs' (by simpa using h0'),
    iteratedFDerivWithin_of_isOpen _ hvo h0'] at key
  rw [key]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  congr 1
  funext l
  simp [slotEmbedding_single ι hι]
end YangMills.Construction.ColdStepAtMirrorFrames
end
