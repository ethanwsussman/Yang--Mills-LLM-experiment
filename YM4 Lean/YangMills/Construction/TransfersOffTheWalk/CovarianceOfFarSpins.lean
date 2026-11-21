import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfTwoGases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
def DependsOnlyOn {I : Type} {S : I → Type} (M : Finset I) (F : (∀ i, S i) → ℝ) : Prop :=
  ∀ σ σ', (∀ i ∈ M, σ i = σ' i) → F σ = F σ'
def CovarianceDecayStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ)
    (h : A.IsActivityBounded m G z) (c : I → I → ℝ) (w : I → ℝ) (M₁ M₂ : Finset I) (F₁ F₂ : (∀ i, S i) → ℝ) (B₁ B₂ : ℝ),
    A.HasDobrushinColumns m h.measurable_weightDensity c w → (∀ i ∈ M₁, 1 ≤ w i) → Measurable F₁ → Measurable F₂ →
    (∀ σ, |F₁ σ| ≤ B₁) → (∀ σ, |F₂ σ| ≤ B₂) → DependsOnlyOn M₁ F₁ → DependsOnlyOn M₂ F₂ →
    |∫ σ, F₁ σ * F₂ σ ∂A.gibbsLaw m G - (∫ σ, F₁ σ ∂A.gibbsLaw m G) * ∫ σ, F₂ σ ∂A.gibbsLaw m G| ≤
      96 * B₁ * B₂ * ∑ i ∈ M₂, w i * z i
end YangMills.Construction.Dobrushin
end
