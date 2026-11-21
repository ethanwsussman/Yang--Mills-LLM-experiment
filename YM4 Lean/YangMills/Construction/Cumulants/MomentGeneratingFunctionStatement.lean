import YangMills.Construction.Lattice.WilsonGibbsMeasure
import Mathlib
open MeasureTheory Set
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace Cumulants
def MomentGeneratingFunctionRegularity : Prop :=
  ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ],
    (∀ (n : ℕ) (f : Fin n → Ω → ℝ), (∀ i, Measurable (f i)) → (∀ i, ∃ C, ∀ ω, |f i ω| ≤ C) →
      Differentiable ℂ (momentGeneratingFunction μ f) ∧
      momentGeneratingFunction μ f 0 = 1 ∧
      (∃ U ∈ 𝓝 (0 : Fin n → ℂ), (∀ z ∈ U, momentGeneratingFunction μ f z ∈ Complex.slitPlane) ∧
        DifferentiableOn ℂ (fun z => Complex.log (momentGeneratingFunction μ f z)) U) ∧
      (mixedCumulant μ f).im = 0) ∧
    ∀ f g : Ω → ℝ, Measurable f → Measurable g → (∃ C, ∀ ω, |f ω| ≤ C) → (∃ C, ∀ ω, |g ω| ≤ C) →
      mixedCumulant μ ![f, g] = (((∫ ω, f ω * g ω ∂μ) - (∫ ω, f ω ∂μ) * ∫ ω, g ω ∂μ : ℝ) : ℂ)
end Cumulants
end YangMills.Construction
