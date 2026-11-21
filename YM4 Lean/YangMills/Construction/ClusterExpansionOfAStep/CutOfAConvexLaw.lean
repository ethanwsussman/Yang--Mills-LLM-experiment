import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
def RestrictedLawMeanBound : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ A O c C₁ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) → 2 * m ≤ c →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) →
    ∀ (X Z : Finset ι) (F : BondField ι → ℝ), Measurable F →
      (∀ η η' : BondField ι, (∀ b ∈ Z, η b = η' b) → F η = F η') →
      (∀ η η' : BondField ι, (∀ b, ‖η b‖ < ρ) → (∀ b, ‖η' b‖ < ρ) → |F η - F η'| ≤ O) →
      |ballExpectation (cutoffFactor ρ p) Ψ F - ballExpectation (cutoffFactor ρ p) (restrictedPotential c X Ψ) F| ≤
        4 * ρ * (1 + A) * O * ∑ b ∈ Z, ∑ b', restrictedGradBound ρ c C₁ X K b' * Real.exp (-(κ * d b b'))
end YangMills.Construction.ClusterExpansionOfAStep
end
