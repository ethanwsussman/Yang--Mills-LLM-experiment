import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def GibbsMeanBounds : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (A f g h l : Ω → ℝ) (c d e r : ℝ), 0 ≤ c → 0 ≤ d → 0 ≤ e →
    0 ≤ r → (∀ᵐ ω ∂μ, |f ω| ≤ c) → (∀ᵐ ω ∂μ, |g ω| ≤ d) → (∀ᵐ ω ∂μ, |h ω| ≤ e) →
    (∀ᵐ ω ∂μ, |l ω| ≤ r) →
    |gibbsMean μ A f| ≤ c ∧ |gibbsCovariance μ A f g| ≤ 2 * (c * d) ∧
      |gibbsCumulantThree μ A f g h| ≤ 6 * (c * d * e) ∧
      |gibbsCumulantFour μ A f g h l| ≤ 26 * (c * d * e * r)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
