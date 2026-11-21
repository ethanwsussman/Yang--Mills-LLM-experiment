import YangMills.Construction.ColdStepAtMirrorFrames.AnalyticAlongFields
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.ColdStepAtMirrorFrames
theorem analyticAlongDirectionFields : AnalyticAlongDirectionFields := by
  classical
  intro F j k E _ _ G U J ξ hξ hG
  let ι : Type := Σ l : Fin k, ↥(J l)
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  let n := Fintype.card ι
  let b : Fin n → F.Site j × Fin 4 := fun q => ((e.symm q).2 : F.Site j × Fin 4)
  let X : Fin n → imaginaryQuaternions := fun q => ξ (e.symm q).1 (b q).1 (b q).2
  let f : (Fin n → ℝ) → E := fun σ => G (leftTranslate (bondSpread b X σ) U)
  have hf : AnalyticAt ℝ f 0 := hG n b X
  let P : (Fin k → ℝ) →L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearMap.pi fun q => ContinuousLinearMap.proj (e.symm q).1
  have hP : ∀ τ q, P τ q = τ (e.symm q).1 := fun τ q => rfl
  have hb : ∀ x : ι, b (e x) = x.2 := fun x => by
    change ((e.symm (e x)).2 : F.Site j × Fin 4) = x.2
    rw [Equiv.symm_apply_apply]
  have hX : ∀ x : ι, X (e x) = ξ x.1 (x.2 : F.Site j × Fin 4).1 (x.2 : F.Site j × Fin 4).2 :=
    fun x => by
      change ξ (e.symm (e x)).1 (b (e x)).1 (b (e x)).2 = _
      rw [hb, Equiv.symm_apply_apply]
  have hP' : ∀ (τ : Fin k → ℝ) (x : ι), P τ (e x) = τ x.1 := fun τ x => by simp [hP]
  have hspread : ∀ τ : Fin k → ℝ, bondSpread b X (P τ) = fun z i => ∑ l, τ l • ξ l z i := by
    intro τ
    funext z i
    simp only [bondSpread]
    rw [← e.sum_comp]
    simp only [hb, hX, hP']
    rw [Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun l _ => ?_
    by_cases hz : (z, i) ∈ J l
    · rw [Finset.sum_eq_single (⟨(z, i), hz⟩ : ↥(J l))]
      · simp
      · intro p _ hp
        rw [if_neg]
        intro hc
        exact hp (Subtype.ext hc)
      · simp
    · rw [hξ l z i hz, smul_zero]
      refine Finset.sum_eq_zero fun p _ => ?_
      split_ifs with hc
      · exact absurd (hc ▸ p.2) hz
      · rfl
  have hcomp : (fun τ : Fin k → ℝ => G (leftTranslate (fun z i => ∑ l, τ l • ξ l z i) U)) = f ∘ P := by
    funext τ
    simp only [Function.comp, f, hspread]
  rw [hcomp]
  have hP0 : AnalyticAt ℝ f (P 0) := by simpa using hf
  exact hP0.comp (P.analyticAt 0)
end YangMills.Construction.ColdStepAtMirrorFrames
end
