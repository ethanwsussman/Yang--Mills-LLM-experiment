import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConvexBallLaws
open ColdStepAtMirrorFrames
def SecondMomentBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ W : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b₀, ∑ b, Real.exp (-(2 * κ * d b b₀)) ≤ W) →
    ∀ b₀ : ι, ballExpectation (cutoffFactor ρ p) Ψ (fun η => ‖η b₀‖ ^ 2) ≤
      6 * W / m + (m ^ 2)⁻¹ * ∑ b, Real.exp (-(2 * κ * d b b₀)) * bondGradNorm Ψ b 0 ^ 2
end ConvexBallLaws
end YangMills.Construction
end
