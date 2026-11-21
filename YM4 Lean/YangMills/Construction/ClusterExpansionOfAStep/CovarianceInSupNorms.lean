import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConvexMeasures
open ColdStepAtMirrorFrames
def covarianceSupNormBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ K →
    ∀ (f g : BondField ι → ℝ) (Bf Bg : ι → ℝ), ContDiff ℝ 1 f → ContDiff ℝ 1 g →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm f b η ≤ Bf b) →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm g b η ≤ Bg b) →
      |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤
        m⁻¹ * ∑ b, ∑ b', Bf b * Real.exp (-(κ * d b b')) * Bg b'
end ConvexMeasures
end YangMills.Construction
end
