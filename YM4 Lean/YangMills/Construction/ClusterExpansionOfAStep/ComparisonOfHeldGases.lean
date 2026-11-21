import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfTwoGases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
def vacantSpinComparisonStatement : Prop :=
  ∀ (I₁ I₂ J : Type) [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype J] [DecidableEq J]
    (S₁ : I₁ → Type) (S₂ : I₂ → Type) (T : J → Type) [∀ i, MeasurableSpace (S₁ i)] [∀ i, MeasurableSpace (S₂ i)]
    [∀ j, MeasurableSpace (T j)]
    (P₁ : PairConstraint S₁) (P₂ : PairConstraint S₂) (P : PairConstraint T)
    (m₁ m₁' : ∀ i, Measure (S₁ i)) (m₂ m₂' : ∀ i, Measure (S₂ i)) (μ : ∀ j, Measure (T j))
    [∀ i, SigmaFinite (m₁ i)] [∀ i, SigmaFinite (m₁' i)] [∀ i, SigmaFinite (m₂ i)] [∀ i, SigmaFinite (m₂' i)]
    [∀ j, SigmaFinite (μ j)]
    (G₁ : (∀ i, S₁ i) → ℝ) (G₂ : (∀ i, S₂ i) → ℝ) (z₁ : I₁ → ℝ) (z₂ : I₂ → ℝ)
    (e₁ : J → I₁) (e₂ : J → I₂) (v₁ : ∀ j, T j ≃ᵐ S₁ (e₁ j)) (v₂ : ∀ j, T j ≃ᵐ S₂ (e₂ j))
    (c₁ : I₁ → I₁ → ℝ) (c₂ : I₂ → I₂ → ℝ) (w₁ : I₁ → ℝ) (w₂ : I₂ → ℝ) (b E : J → ℝ)
    (M₁ H₁ : Finset I₁) (M₂ H₂ : Finset I₂) (F₁ : (∀ i, S₁ i) → ℝ) (F₂ : (∀ i, S₂ i) → ℝ)
    (h₁ : P₁.IsActivityBounded m₁ G₁ z₁) (h₂ : P₂.IsActivityBounded m₂ G₂ z₂),
    Function.Injective e₁ → Function.Injective e₂ → P₁.IsVacantOffRange m₁ m₁' e₁ → P₂.IsVacantOffRange m₂ m₂' e₂ →
    (∀ i ∈ H₁, m₁ i = Measure.dirac (P₁.vacant i)) → (∀ i ∈ H₂, m₂ i = Measure.dirac (P₂.vacant i)) →
    (∀ j, v₁ j (P.vacant j) = P₁.vacant (e₁ j)) → (∀ j, v₂ j (P.vacant j) = P₂.vacant (e₂ j)) →
    (∀ j j' s t, j ≠ j' → (P.compatible j j' s t ↔ P₁.compatible (e₁ j) (e₁ j') (v₁ j s) (v₁ j' t))) →
    (∀ j j' s t, j ≠ j' → (P.compatible j j' s t ↔ P₂.compatible (e₂ j) (e₂ j') (v₂ j s) (v₂ j' t))) →
    (∀ j, MeasurePreserving (v₁ j) (μ j) (m₁ (e₁ j))) → (∀ j, MeasurePreserving (v₂ j) (μ j) (m₂ (e₂ j))) →
    P₁.HasDobrushinColumns m₁ h₁.measurable_weightDensity c₁ w₁ →
    P₂.HasDobrushinColumns m₂ h₂.measurable_weightDensity c₂ w₂ →
    P₁.IsLocalObservable M₁ w₁ F₁ → P₂.IsLocalObservable M₂ w₂ F₂ →
    (∀ τ, F₁ (P₁.embedConfig e₁ (fun j => v₁ j) τ) = F₂ (P₂.embedConfig e₂ (fun j => v₂ j) τ)) →
    (∀ j, 0 ≤ b j) →
    (∀ j, 2 * (z₁ (e₁ j) + z₂ (e₂ j)) ≤ b j ∨
      (1 ≤ E j ∧ z₁ (e₁ j) ≤ 1 ∧ z₂ (e₂ j) ≤ 1 ∧ 8 * (E j - 1) * max (z₁ (e₁ j)) (z₂ (e₂ j)) ≤ b j ∧
        ∀ τ s, P.IsAdmissible (Function.update τ j s) →
          G₁ (P₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j s)) *
              G₂ (P₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j (P.vacant j))) ≤
            E j * (G₁ (P₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j (P.vacant j))) *
              G₂ (P₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j s))) ∧
          G₂ (P₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j s)) *
              G₁ (P₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j (P.vacant j))) ≤
            E j * (G₂ (P₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j (P.vacant j))) *
              G₁ (P₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j s))))) →
    |∫ σ, F₁ σ ∂P₁.gibbsLaw m₁ G₁ - ∫ σ, F₂ σ ∂P₂.gibbsLaw m₂ G₂| ≤
      8 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e₁ j ≠ i) ∧ i ∉ H₁), w₁ i * z₁ i +
        8 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e₂ j ≠ i) ∧ i ∉ H₂), w₂ i * z₂ i +
        4 * ∑ j, w₁ (e₁ j) * b j
end YangMills.Construction.Dobrushin
end
