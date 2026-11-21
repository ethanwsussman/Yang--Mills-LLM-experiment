import YangMills.Construction.SummableBoundsOfTheFlow.ScaledExponentIsTheExponentOfTheStep
import YangMills.Construction.SummableBoundsOfTheFlow.TheDensitiesAreMeansAtAScale
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames MeasureTheory Set
namespace ScaledVariables
variable {F : BlockFrame}
private theorem cutoffMean_congr (ρ : ℝ) (p : ℝ → ℝ) (Ψ H H' : StepVariable (finiteCells F) → ℝ)
    (h : ∀ η, (∀ b, ‖η b‖ < ρ) → H η = H' η) : cutoffMean ρ p Ψ H = cutoffMean ρ p Ψ H' := by
  unfold cutoffMean
  congr 1
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun η => ?_
  by_cases hη : ∀ b, ‖η b‖ < ρ
  · simp only [h η hη]
  · push_neg at hη
    obtain ⟨b, hb⟩ := hη
    have h0 : cutoffWeight ρ p η = 0 := by
      unfold cutoffWeight
      apply Finset.prod_eq_zero (Finset.mem_univ b)
      unfold cutoffFactor
      rw [if_neg (not_lt.mpr hb)]
    simp [h0]
abbrev _root_.YangMills.SharedProofs.p130533 := @cutoffMean_congr
theorem densitiesAreRescaledMeans_of_exponentAgrees (hE : RescaledExponentAgrees) :
    DensitiesAreRescaledMeans := by
  refine EventuallyOrdered.mono hE ?_
  rintro T hT hn ⟨l₀, hl₀, gE⟩
  refine ⟨l₀, hl₀, ?_⟩
  intro t F V f l Y hF hV hl hll
  have h1 : ∀ θ : ℝ, cutoffMean T.ballRadius T.p
      (fun η => θ * stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f 0 V η +
        (1 - θ) * totalQuadratic T.lam (l⁻¹ ^ 2) η)
      (fun η => cellExponent true T.a T.ρA (l⁻¹ ^ 2) 0 Y V η - cellQuadratic T.lam (l⁻¹ ^ 2) Y η) =
      observableMean T.a T.ρA T.ballRadius T.lam T.p f (.interpolated θ)
        (fun l ζ V' => rescaledCellRemainder T.a T.ρA T.lam l Y V' ζ) l V := by
    intro θ
    simp only [observableMean, rescaledMean, stepLawExponent]
    apply cutoffMean_congr
    intro η hη
    have hball : MemScaledBalls T.ballRadius l (l⁻¹ • η) := by
      intro b
      rw [Pi.smul_apply, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hl), ← mul_assoc,
        mul_inv_cancel₀ hl.ne', one_mul]
      exact hη b
    obtain ⟨-, g1, g2⟩ := gE t F V f 0 l Y (l⁻¹ • η) hF hV hl hll hball
    have hback : l • (l⁻¹ • η) = η := by
      rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    rw [hback] at g1 g2
    unfold rescaledCellRemainder
    rw [g1, g2]
  have h2 : ∀ θ : ℝ, cutoffMean T.ballRadius T.p (stepExponent true T.a T.ρA (l⁻¹ ^ 2) 0 f θ V)
      (fun η => cellCentredExpansion true T.a T.ρA 0 f Y η V) =
      observableMean T.a T.ρA T.ballRadius T.lam T.p f (.tilted θ)
        (fun l ζ V' => rescaledCellExpansion T.a T.ρA f l Y V' ζ) l V := by
    intro θ
    simp only [observableMean, rescaledMean, stepLawExponent, rescaledCellExpansion]
    have hback : ∀ η : StepVariable (finiteCells F), l • (l⁻¹ • η) = η := by
      intro η
      rw [smul_smul, mul_inv_cancel₀ hl.ne', one_smul]
    simp only [hback]
  refine ⟨h1, h2, ?_, ?_⟩
  · unfold interactionDensity
    simp only [h1]
  · unfold expansionDensity
    simp only [h2]
end ScaledVariables
end YangMills.Construction
end
