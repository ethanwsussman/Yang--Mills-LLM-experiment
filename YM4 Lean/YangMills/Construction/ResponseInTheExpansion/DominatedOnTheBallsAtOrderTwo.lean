import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.LinearResponse
open ColdStepAtMirrorFrames
def DominatedOfContDiffTwoOnClosedBalls : Prop :=
  ∀ (ι : Type) [Fintype ι] (k : ℕ) (ρ : ℝ) (μ : Measure (BondField ι))
    (G : (Fin k → ℝ) × BondField ι → ℝ),
    (∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ) → (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → ContDiffAt ℝ 2 G (0, η)) →
    ∃ r M : ℝ, 0 < r ∧ IsDominatedSmoothFamily μ 2 (Metric.ball 0 r) M fun τ η => G (τ, η)
end YangMills.Construction.LinearResponse
end
