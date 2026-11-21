import YangMills.Construction.EuclideanAnalysis.FunctionsAndDistributions
import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.EuclideanAnalysis.HolomorphicCharFun
def ExpMomentsOfHolomorphicCharFun : Prop :=
  ∀ (μ : Measure ℝ) [IsFiniteMeasure μ] (ρ : ℝ) (g : ℂ → ℂ), 0 < ρ →
    DifferentiableOn ℂ g (Metric.ball 0 ρ) →
    (∀ t ∈ Set.Ioo (-ρ) ρ, YangMills.Construction.EuclideanAnalysis.measureCharFun μ t = g t) →
    ∀ a : ℝ, 0 ≤ a → a < ρ →
      ∫⁻ q, ENNReal.ofReal (Real.exp (a * |q|)) ∂μ < ∞ ∧
        ((∫ q, Real.cosh (a * q) ∂μ : ℝ) : ℂ) =
          (1 / 2 : ℂ) * (g (Complex.I * a) + g (-(Complex.I * a)))
end YangMills.Construction.EuclideanAnalysis.HolomorphicCharFun
