import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ConvexDecoupling
open ColdStepAtMirrorFrames
def ProductMeanNearMeanProduct : Prop :=
  ∀ (ι α : Type) [Fintype ι] [DecidableEq ι] [DecidableEq α] (ρ m κ A c C₁ : ℝ) (d : ι → ι → ℝ)
    (Ψ : BondField ι → ℝ) (K : ι → ι → ℝ) (p : ℝ → ℝ),
    0 < ρ → 0 < m → 0 ≤ κ → IsCutoff ρ p → IsPseudoMetricOnBonds d → IsUniformlyConvexDecaying ρ m κ d Ψ K →
    (∀ b, ∑ b' ∈ Finset.univ.erase b, K b b' * Real.exp (κ * d b b') ≤ A * m) → 2 * m ≤ c →
    (∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → ∀ b, bondGradNorm Ψ b η ≤ C₁) →
    ∀ (I : Finset α) (Λ X : α → Finset ι) (F : α → BondField ι → ℝ) (P : α → ℝ) (B : ι → ℝ),
      (∀ i ∈ I, ∀ j ∈ I, i ≠ j → Disjoint (Λ i) (Λ j)) → (∀ i ∈ I, X i ⊆ Λ i) →
      (∀ i ∈ I, Measurable (F i)) →
      (∀ i ∈ I, ∀ η η' : BondField ι, (∀ b ∈ X i, η b = η' b) → F i η = F i η') →
      (∀ i ∈ I, ∀ η : BondField ι, (∀ b, ‖η b‖ < ρ) → |F i η| ≤ P i) →
      (∀ i ∈ I, ∀ b ∈ Λ i, ρ * ∑ b' ∈ Finset.univ \ Λ i, K b b' ≤ B b) →
      (∀ b, (∀ i ∈ I, b ∉ Λ i) → C₁ + c * ρ ≤ B b) →
      |ballExpectation (cutoffFactor ρ p) Ψ (fun η => ∏ i ∈ I, F i η) -
          ∏ i ∈ I, ballExpectation (cutoffFactor ρ p) Ψ (F i)| ≤
        4 * ρ * (1 + A) * (2 * (1 + I.card) * ∏ i ∈ I, P i) *
          ∑ b ∈ I.biUnion X, ∑ b', B b' * Real.exp (-(κ * d b b'))
end ConvexDecoupling
end YangMills.Construction
end
