import YangMills.Construction.ClusterExpansionOfAStep.LawsOnProductsOfBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open ColdStepAtMirrorFrames
def SharedMarginalMeanBound : Prop :=
  ∀ (ι ι' ι₀ : Type) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι₀] [DecidableEq ι₀]
    (ρ m κ A O c C₁ : ℝ) (d : ι → ι → ℝ) (d' : ι' → ι' → ℝ) (d₀ : ι₀ → ι₀ → ℝ)
    (Ψ : BondField ι → ℝ) (Ψ' : BondField ι' → ℝ) (K : ι → ι → ℝ) (K' : ι' → ι' → ℝ) (p : ℝ → ℝ)
    (j : ι₀ → ι) (j' : ι₀ → ι'),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsPseudoMetricOnBonds d' →
    Function.Injective j → Function.Injective j' →
    (∀ a b, d₀ a b = d (j a) (j b)) → (∀ a b, d₀ a b = d' (j' a) (j' b)) →
    IsUniformlyConvexDecaying ρ m κ d Ψ K → IsUniformlyConvexDecaying ρ m κ d' Ψ' K' →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K' b b' * Real.exp (κ * d' b b') ≤ A * m) → 2 * m ≤ c →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) →
    (∀ η : BondField ι', (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ' b η ≤ C₁) →
    ∀ (Z : Finset ι₀) (F : BondField ι₀ → ℝ) (B : ι₀ → ℝ), Measurable F →
      (∀ ξ ξ' : BondField ι₀, (∀ a ∈ Z, ξ a = ξ' a) → F ξ = F ξ') →
      (∀ ξ ξ' : BondField ι₀, (∀ a, ‖ξ a‖ < ρ) → (∀ a, ‖ξ' a‖ < ρ) → |F ξ - F ξ'| ≤ O) →
      (∀ ξ : BondField ι₀, (∀ a, ‖ξ a‖ < ρ) → ∀ a,
        bondGradNorm (fun ζ => Ψ' (extendByZero j' ζ) - Ψ (extendByZero j ζ)) a ξ ≤ B a) →
      |ballExpectation (cutoffFactor ρ p) Ψ (fun η => F fun a => η (j a)) -
          ballExpectation (cutoffFactor ρ p) Ψ' (fun η => F fun a => η (j' a))| ≤
        4 * ρ * (1 + A) * O *
          (∑ a ∈ Z, ∑ b, restrictedGradBound ρ c C₁ (Finset.univ.image j) K b * Real.exp (-(κ * d (j a) b)) +
            ∑ a ∈ Z, ∑ b, restrictedGradBound ρ c C₁ (Finset.univ.image j') K' b *
              Real.exp (-(κ * d' (j' a) b)) +
            ∑ a ∈ Z, ∑ a', B a' * Real.exp (-(κ * d₀ a a')))
end YangMills.Construction.ClusterExpansionOfAStep
end
