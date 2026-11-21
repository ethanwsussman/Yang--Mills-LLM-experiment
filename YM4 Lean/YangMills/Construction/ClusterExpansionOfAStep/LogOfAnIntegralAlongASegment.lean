import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace Interpolation
def tiltedMean {α : Type} [MeasurableSpace α] (μ : Measure α) (w f g G : α → ℝ) (t : ℝ) : ℝ :=
  (∫ a, G a * (w a * Real.exp (f a + t * g a)) ∂μ) / ∫ a, w a * Real.exp (f a + t * g a) ∂μ
def LogIntegralExpInterpolationStatement : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (μ : Measure α) (w f g : α → ℝ) (M : ℝ), μ ≠ 0 → Integrable w μ →
    (∀ᵐ a ∂μ, 0 < w a) → AEStronglyMeasurable f μ → AEStronglyMeasurable g μ →
    (∀ᵐ a ∂μ, |f a| ≤ M) → (∀ᵐ a ∂μ, |g a| ≤ M) →
    (∀ t : ℝ, 0 < ∫ a, w a * Real.exp (f a + t * g a) ∂μ) ∧
    (∀ G : α → ℝ, AEStronglyMeasurable G μ → (∃ K : ℝ, ∀ᵐ a ∂μ, |G a| ≤ K) →
      Continuous (tiltedMean μ w f g G)) ∧
    Real.log (∫ a, w a * Real.exp (f a + g a) ∂μ) - Real.log (∫ a, w a * Real.exp (f a) ∂μ) =
      ∫ t in (0 : ℝ)..1, tiltedMean μ w f g g t
end Interpolation
end YangMills.Construction
end
