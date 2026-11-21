import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def BallCovarianceBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ K →
    ∀ f g : BondField ι → ℝ, ContDiff ℝ 1 f → ContDiff ℝ 1 g →
      |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤ m⁻¹ * ∑ b, ∑ b',
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
          ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b')
end YangMills.Construction.ColdStepAtMirrorFrames
end
