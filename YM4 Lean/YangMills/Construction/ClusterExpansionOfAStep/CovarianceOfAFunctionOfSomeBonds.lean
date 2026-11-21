import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConvexMeasures
open ColdStepAtMirrorFrames
def covarianceLocalMeasurableBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ A O : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) →
    ∀ (X : Finset ι) (F G : BondField ι → ℝ) (B : ι → ℝ), Measurable F →
      (∀ η η' : BondField ι, (∀ b ∈ X, η b = η' b) → F η = F η') →
      (∀ η η' : BondField ι, (∀ b, ‖η b‖ < ρ) → (∀ b, ‖η' b‖ < ρ) → |F η - F η'| ≤ O) →
      ContDiff ℝ 1 G →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm G b η ≤ B b) →
      |ballCovariance (cutoffFactor ρ p) Ψ F G| ≤
        4 * ρ * (1 + A) * O * ∑ b ∈ X, ∑ b', B b' * Real.exp (-(κ * d b b'))
end ConvexMeasures
end YangMills.Construction
end
