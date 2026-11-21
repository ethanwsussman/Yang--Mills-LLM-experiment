import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def GaussianMomentBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ W : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (χ : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsRadialCutoff ρ χ → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    (∀ (b : ι) (e : BondVector), |bondPartialDeriv Ψ b 0 e| ≤ Real.sqrt m * ‖e‖) →
    ∀ (q : ℕ) (b₀ : ι), ballExpectation χ Ψ (fun η => ‖η b₀‖ ^ (2 * q)) ≤
      (∏ k ∈ Finset.range q, (4 * (k : ℝ) + 8 * W)) / m ^ q
end YangMills.Construction.ColdStepAtMirrorFrames
end
