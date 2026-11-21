import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.DerivativesOfAWeightedMean
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def DominatedFamilyOnClosedBalls : Prop :=
  ∀ (ι : Type) [Fintype ι] (k : ℕ) (ρ : ℝ) (μ : Measure (BondField ι))
    (G : (Fin k → ℝ) × (ℝ × BondField ι) → ℝ),
    (∀ᵐ η ∂μ, ∀ b, ‖η b‖ ≤ ρ) →
    (∀ (v : ℝ) (η : BondField ι), v ∈ Set.Icc (0 : ℝ) 1 → (∀ b, ‖η b‖ ≤ ρ) →
      ContDiffAt ℝ 3 G (0, v, η)) →
    ∃ r M : ℝ, 0 < r ∧ ∀ v ∈ Set.Icc (0 : ℝ) 1,
      IsDominatedSmoothFamily μ 3 (Metric.ball 0 r) M fun τ η => G (τ, v, η)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
