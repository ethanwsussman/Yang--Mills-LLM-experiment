import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.SummableBoundsOfTheFlow.ObservablesOfAConvexMeasure
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames YangMills.Construction.ConvexObservables
namespace YangMills.Construction.ConvexObservables
def covarianceOpenBallsStatement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ m κ d Ψ K →
    ∀ f g : BondField ι → ℝ,
      ContDiffOn ℝ 1 f {η | ∀ b, ‖η b‖ < ρ} → ContDiffOn ℝ 1 g {η | ∀ b, ‖η b‖ < ρ} →
      Integrable (fun η => f η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) Ψ) →
      Integrable (fun η => g η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) Ψ) →
      (∀ b, Integrable (fun η => bondGradNorm f b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) Ψ)) →
      (∀ b, Integrable (fun η => bondGradNorm g b η ^ 2) (normalizedBallLaw (cutoffFactor ρ p) Ψ)) →
      |ballCovariance (cutoffFactor ρ p) Ψ f g| ≤ m⁻¹ * ∑ b, ∑ b',
        ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm f b) * Real.exp (-(κ * d b b')) *
          ballL2Norm (cutoffFactor ρ p) Ψ (bondGradNorm g b')
end YangMills.Construction.ConvexObservables
end
