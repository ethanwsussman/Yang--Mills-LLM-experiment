import YangMills.Construction.SummableBoundsOfTheFlow.TheCurvatureOfTheScaledMeansIsTheirCoefficient
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansAreSmoothInTheScale
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirBounds
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansHaveTheirDerivatives
import YangMills.Construction.SummableBoundsOfTheFlow.TheScaledMeansTendToTheirGaussianMeans
import YangMills.Construction.SummableBoundsOfTheFlow.TheSlopeOfTheScaledMeansVanishes
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepDensities
theorem scaledMeanDeriv_holds (h₁ : ScaledVariables.scaledMeansSmoothInScale)
    (h₂ : ScaledVariables.scaledMeansBounded) (h₃ : ScaledVariables.scaledMeansTendToGaussianMeans)
    (h₄ : ScaledVariables.ObservableMeanSlopeVanishes)
    (h₅ : ScaledVariables.scaledMeanSecondDerivTendsToCoeff) :
    scaledMeanDerivStatement := by
  unfold ScaledVariables.scaledMeansSmoothInScale ScaledVariables.ForallSmoothObservables at h₁
  unfold ScaledVariables.scaledMeansBounded ScaledVariables.ForallSmoothObservables at h₂
  unfold ScaledVariables.scaledMeansTendToGaussianMeans ScaledVariables.ForallSmoothObservables at h₃
  unfold ScaledVariables.ObservableMeanSlopeVanishes ScaledVariables.ForallSmoothObservables at h₄
  unfold ScaledVariables.scaledMeanSecondDerivTendsToCoeff ScaledVariables.ForallSmoothObservables at h₅
  unfold scaledMeanDerivStatement
  refine ColdStepAtMirrorFrames.EventuallyOrdered.mono (ColdStepAtMirrorFrames.EventuallyOrdered.and h₁
    (ColdStepAtMirrorFrames.EventuallyOrdered.and h₂ (ColdStepAtMirrorFrames.EventuallyOrdered.and h₃
    (ColdStepAtMirrorFrames.EventuallyOrdered.and h₄ h₅)))) ?_
  rintro T - - ⟨g₁, g₂, g₃, g₄, g₅⟩ e
  obtain ⟨a₁, c₁, p₁, q₁, k₁⟩ := g₁ e
  obtain ⟨a₂, C, p₂, pC, g₂⟩ := g₂ e
  obtain ⟨a₃, c₃, p₃, q₃, k₃⟩ := g₃ e
  obtain ⟨a₄, c₄, p₄, q₄, k₄⟩ := g₄ e
  obtain ⟨a₅, c₅, p₅, q₅, k₅⟩ := g₅ e
  refine ⟨min a₁ (min a₂ (min a₃ (min a₄ a₅))), C, by positivity, pC,
    fun l₁ hl hle t f F V Y law K Ob k c X hf hF hV hL hK hO hX => ?_⟩
  have e₁ : l₁ ≤ a₁ := le_trans hle (min_le_left _ _)
  have e₂ : l₁ ≤ a₂ := le_trans hle (le_trans (min_le_right _ _) (min_le_left _ _))
  have e₃ : l₁ ≤ a₃ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have e₄ : l₁ ≤ a₄ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_left _ _))))
  have e₅ : l₁ ≤ a₅ := le_trans hle (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
    (le_trans (min_le_right _ _) (min_le_right _ _))))
  exact ⟨k₁ l₁ hl e₁ t f F V Y law K Ob k c X hf hF hV hL hK hO hX,
    g₂ l₁ hl e₂ t f F V Y law K Ob k c X hf hF hV hL hK hO hX,
    k₃ l₁ hl e₃ t f F V Y law K Ob k c X hf hF hV hL hK hO hX,
    k₄ l₁ hl e₄ t f F V Y law K Ob k c X hf hF hV hL hK hO hX,
    k₅ l₁ hl e₅ t f F V Y law K Ob k c X hf hF hV hL hK hO hX⟩
end YangMills.Construction.StepDensities
end
