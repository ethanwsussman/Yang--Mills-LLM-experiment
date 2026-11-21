import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace YangMills.Construction.Cumulants
def logLaplaceTransform {Ξ ι E : Type} [MeasurableSpace Ξ] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (L : ι → E →L[ℝ] ℝ) (θ : E) : ℝ :=
  Real.log (∫ ξ, w ξ * Real.exp (∑ i, u i ξ * L i θ) ∂μ)
def CumulantBounds : Prop :=
  ∀ (Ξ ι E : Type) [MeasurableSpace Ξ] [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ξ) (w : Ξ → ℝ) (u : ι → Ξ → ℝ) (L : ι → E →L[ℝ] ℝ) (B : ℝ),
    (∀ i, Measurable (u i)) → (∀ i ξ, |u i ξ| ≤ B) → (∀ ξ θ, |∑ i, u i ξ * L i θ| ≤ ‖θ‖) →
    Integrable w μ → (∀ ξ, 0 ≤ w ξ) → 0 < ∫ ξ, w ξ ∂μ →
    ContDiff ℝ ∞ (logLaplaceTransform μ w u L) ∧
    ∀ θ, ‖iteratedFDeriv ℝ 1 (logLaplaceTransform μ w u L) θ‖ ≤ 1 ∧
      ‖iteratedFDeriv ℝ 2 (logLaplaceTransform μ w u L) θ‖ ≤ 2 ∧
      ‖iteratedFDeriv ℝ 3 (logLaplaceTransform μ w u L) θ‖ ≤ 6
end YangMills.Construction.Cumulants
end
