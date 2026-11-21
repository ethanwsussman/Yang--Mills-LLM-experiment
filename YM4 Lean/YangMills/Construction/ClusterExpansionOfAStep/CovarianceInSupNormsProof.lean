import YangMills.Construction.ClusterExpansionOfAStep.CovarianceInSupNorms
import YangMills.Construction.ClusterExpansionOfAStep.FactorOfAClassIsOneRuleProof
import YangMills.Construction.ColdStepAtMirrorFrames.CovarianceOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ConvexMeasures
open ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι]
theorem cutoffFactor_nonneg (ρ : ℝ) (p : ℝ → ℝ) (u : ℝ) : 0 ≤ cutoffFactor ρ p u := by apply _root_.YangMills.Construction.CoarseFactorLocality.cutoffFactor_nonneg <;> assumption
theorem ballDensity_nonneg (ρ : ℝ) (p : ℝ → ℝ) (Ψ : BondField ι → ℝ) (η : BondField ι) :
    0 ≤ ballDensity (cutoffFactor ρ p) Ψ η :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => cutoffFactor_nonneg ρ p _) (Real.exp_pos _).le
theorem norm_lt_of_ballDensity_ne_zero {ρ : ℝ} {p : ℝ → ℝ} {Ψ : BondField ι → ℝ} {η : BondField ι}
    (hη : ballDensity (cutoffFactor ρ p) Ψ η ≠ 0) (b : ι) : ‖η b‖ < ρ := by
  by_contra hc
  apply hη
  unfold ballDensity radialWeightProd
  rw [Finset.prod_eq_zero (Finset.mem_univ b) (by simp [cutoffFactor, not_lt.mp hc]), zero_mul]
theorem ballL2Norm_le {ρ B : ℝ} {p : ℝ → ℝ} {Ψ f : BondField ι → ℝ} (hB : 0 ≤ B)
    (hb : ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |f η| ≤ B) :
    ballL2Norm (cutoffFactor ρ p) Ψ f ≤ B := by
  unfold ballL2Norm
  apply Real.sqrt_le_iff.mpr ⟨hB, ?_⟩
  unfold ballExpectation
  set ϱ := ballDensity (cutoffFactor ρ p) Ψ with hϱ
  have hϱ0 : ∀ η, 0 ≤ ϱ η := ballDensity_nonneg ρ p Ψ
  by_cases hi : Integrable ϱ
  · have hle : ∫ η, f η ^ 2 * ϱ η ≤ ∫ η, B ^ 2 * ϱ η := by
      apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun η => ?_) (hi.const_mul _)
        (Filter.Eventually.of_forall fun η => ?_)
      · exact mul_nonneg (sq_nonneg _) (hϱ0 η)
      · by_cases h0 : ϱ η = 0
        · simp [h0]
        · have h1 := hb η (norm_lt_of_ballDensity_ne_zero h0)
          apply mul_le_mul_of_nonneg_right _ (hϱ0 η)
          exact sq_le_sq' (by linarith [(abs_le.mp h1).1]) (abs_le.mp h1).2
    rw [integral_const_mul] at hle
    exact div_le_of_le_mul₀ (integral_nonneg hϱ0) (sq_nonneg B) hle
  · rw [integral_undef hi]
    simp only [div_zero]
    positivity
theorem covarianceSupNormBound_of_ballCovarianceBound (hcov : BallCovarianceBound) :
    covarianceSupNormBound := by
  intro ι _ _ ρ m κ d Ψ K p hρ hm hκ hp hd hC f g Bf Bg hf hg hBf hBg
  have h0 : ∀ b, ‖(0 : BondField ι) b‖ < ρ := fun b => by simpa using hρ
  have hf0 : ∀ b, 0 ≤ Bf b := fun b => (norm_nonneg _).trans (hBf 0 h0 b)
  have hg0 : ∀ b, 0 ≤ Bg b := fun b => (norm_nonneg _).trans (hBg 0 h0 b)
  have hnf : ∀ b, ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) ≤ Bf b := fun b =>
    ballL2Norm_le (hf0 b) fun η hη => by
      rw [abs_of_nonneg (show 0 ≤ bondGradNorm _ b η from norm_nonneg _)]
      exact hBf η hη b
  have hng : ∀ b, ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b) ≤ Bg b := fun b =>
    ballL2Norm_le (hg0 b) fun η hη => by
      rw [abs_of_nonneg (show 0 ≤ bondGradNorm _ b η from norm_nonneg _)]
      exact hBg η hη b
  refine (hcov ι ρ m κ d Ψ K p hρ hm hκ hp hd hC f g hf hg).trans ?_
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hm.le)
  apply Finset.sum_le_sum
  intro b _
  apply Finset.sum_le_sum
  intro b' _
  have e0 := Real.exp_pos (-(κ * d b b'))
  have n0 : 0 ≤ ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b') := Real.sqrt_nonneg _
  exact mul_le_mul (mul_le_mul_of_nonneg_right (hnf b) e0.le) (hng b') n0
    (mul_nonneg (hf0 b) e0.le)
end YangMills.Construction.ConvexMeasures
end
