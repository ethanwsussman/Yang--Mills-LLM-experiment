import YangMills.Construction.ClusterExpansionOfAStep.BasesExist
import YangMills.Construction.ResponseInTheExpansion.MeanOfScoresOverAStep
import YangMills.Construction.ResponseInTheExpansion.ProductsOfScoresAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
open TorusLumps TorusFields StepCosts
theorem scoreProductStepMean_holds (hP : ResponseInTheExpansion.MeanOfScoreProductsStatement)
    (hB : BaseChoicesNonempty) : ScoreProductStepMean := by
  intro ℓ hfit hLam y n _ W m a v hv
  classical
  set B := baseChoices ℓ (readAtLevel (stepBlockFrame ℓ.side n) 0 W) with hBdef
  have hne : B.Nonempty := hB ℓ hfit hLam n _
  have hcard : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hne).ne'
  have hterm : ∀ b : BaseChoice ℓ.side n, ∫ V : TorusField n,
      (∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore ℓ y W V b c)) *
      stepTransitionDensity ℓ y W b V ∂(fieldHaar n) = if b ∈ B then (1 / (B.card : ℝ)) * ∏ i, a i else 0 := by
    intro b
    by_cases hb : b ∈ B
    · have he : ∀ V : TorusField n, (∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore ℓ y W V b c)) *
          stepTransitionDensity ℓ y W b V =
          (1 / (B.card : ℝ)) * ((∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore ℓ y W V b c)) *
            ∏ c : (stepBlockFrame ℓ.side n).Cell × Fin 4,
              bondKernel ℓ y (readAtLevel (stepBlockFrame ℓ.side n) 0 W)
                (readAtLevel (stepBlockFrame ℓ.side n) 1 V) b c) := by
        intro V
        unfold stepTransitionDensity
        rw [if_pos hb]
        ring
      simp only [he]
      rw [integral_const_mul, hP ℓ y n W b m a v hv, if_pos hb]
    · have he : ∀ V : TorusField n, (∏ i, (a i + ∑ c : TorusBond n, v i c * bondScore ℓ y W V b c)) *
          stepTransitionDensity ℓ y W b V = 0 := by
        intro V
        unfold stepTransitionDensity
        rw [if_neg hb, mul_zero]
      simp only [he]
      simp [hb]
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  field_simp
end YangMills.Construction.WeightedResponses
end
