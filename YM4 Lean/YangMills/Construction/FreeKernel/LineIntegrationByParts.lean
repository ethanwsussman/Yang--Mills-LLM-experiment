import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
open Complex MeasureTheory Filter Topology
def LineFourierIntegrationByParts : Prop :=
  ∀ (n : ℕ) (f : ℝ → ℂ) (ξ : ℝ), ξ ≠ 0 → ContDiff ℝ n f →
    (∀ k : ℕ, k ≤ n → Integrable (iteratedDeriv k f) ∧
      Tendsto (iteratedDeriv k f) atTop (𝓝 0) ∧ Tendsto (iteratedDeriv k f) atBot (𝓝 0)) →
    ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * f θ =
      (I / (ξ : ℂ)) ^ n * ∫ θ : ℝ, Complex.exp (I * (ξ : ℂ) * (θ : ℂ)) * iteratedDeriv n f θ
end YangMills.Construction.FreeKernel
end
