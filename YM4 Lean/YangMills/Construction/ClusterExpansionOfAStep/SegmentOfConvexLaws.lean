import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
def ConvexLawSegmentBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ A O : ℝ) (d : ι → ι → ℝ)
    (Ψ₀ Ψ₁ : BondField ι → ℝ) (K₀ K₁ : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d →
    IsUniformlyConvexDecaying ρ m κ d Ψ₀ K₀ → IsUniformlyConvexDecaying ρ m κ d Ψ₁ K₁ →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K₀ b b' * Real.exp (κ * d b b') ≤ A * m) →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K₁ b b' * Real.exp (κ * d b b') ≤ A * m) →
    ∀ (Z : Finset ι) (F : BondField ι → ℝ) (B : ι → ℝ), Measurable F →
      (∀ η η' : BondField ι, (∀ b ∈ Z, η b = η' b) → F η = F η') →
      (∀ η η' : BondField ι, (∀ b, ‖η b‖ < ρ) → (∀ b, ‖η' b‖ < ρ) → |F η - F η'| ≤ O) →
      (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm (fun ζ => Ψ₁ ζ - Ψ₀ ζ) b η ≤ B b) →
      |ballExpectation (cutoffFactor ρ p) Ψ₁ F - ballExpectation (cutoffFactor ρ p) Ψ₀ F| ≤
        4 * ρ * (1 + A) * O * ∑ b ∈ Z, ∑ b', B b' * Real.exp (-(κ * d b b'))
end YangMills.Construction.ClusterExpansionOfAStep
end
