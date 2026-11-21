import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import YangMills.Construction.ColdStepAtMirrorFrames.LocalTermsOfAMeasureForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
structure AdmissibleMomentBounds {ι P : Type} [Fintype ι] [DecidableEq ι] [Fintype P]
    (ρ m r S : ℝ) (p : ℝ → ℝ) (pos : ι → P) (D : P → P → ℝ) (Φ : BondField ι → ℝ) : Prop where
  second_moment_le : ∀ b, ballExpectation (cutoffFactor ρ p) Φ (fun η => ‖η b‖ ^ 2) ≤ 8 * S / m
  near_moment_le : ∀ z, ballExpectation (cutoffFactor ρ p) Φ (weightedSqNormNear r pos D z) ≤ 8 * S ^ 2 / m
  linear_moment_le : ∀ a : ι → ℝ, (∀ b, 0 ≤ a b) →
    ballExpectation (cutoffFactor ρ p) Φ (fun η => (∑ b, a b * ‖η b‖) ^ 2) ≤ (∑ b, a b) ^ 2 * (8 * S / m)
  covariance_le : ∀ (f g : BondField ι → ℝ) (M A : ℝ) (z : P) (G : ι → ℝ),
    ContDiffOn ℝ 1 f (openPolyball ι ρ) → ContDiffOn ℝ 1 g (openPolyball ι ρ) →
    (∀ η ∈ openPolyball ι ρ, |f η| ≤ M ∧ |g η| ≤ M ∧
      ∀ b, bondGradNorm f b η ≤ M ∧ bondGradNorm g b η ≤ M) → 0 ≤ A → (∀ b, 0 ≤ G b) →
    (∀ b, ballL2Norm (cutoffFactor ρ p) Φ (bondGradNorm f b) ≤ A * Real.exp (-(2 * r * D (pos b) z))) →
    (∀ b, ballL2Norm (cutoffFactor ρ p) Φ (bondGradNorm g b) ≤ G b) →
    |ballCovariance (cutoffFactor ρ p) Φ f g| ≤
      m⁻¹ * A * S * ∑ b, G b * Real.exp (-(r / 2 * D (pos b) z))
def AdmissibleMomentBoundsHold : Prop :=
  ∀ (ι P : Type) [Fintype ι] [DecidableEq ι] [Fintype P] (ρ m r S : ℝ) (p : ℝ → ℝ) (pos : ι → P)
    (D : P → P → ℝ) (Φ : BondField ι → ℝ), 0 < ρ → 0 < m → 0 < r → IsCutoff ρ p → IsPseudoMetricOnBonds D →
    IsAdmissiblePotential ρ m r (fun b b' => D (pos b) (pos b')) Φ →
    (∀ z, ∑ b, Real.exp (-(r / 4 * D (pos b) z)) ≤ S) →
    AdmissibleMomentBounds ρ m r S p pos D Φ
end ColdStepAtMirrorFrames
end YangMills.Construction
end
