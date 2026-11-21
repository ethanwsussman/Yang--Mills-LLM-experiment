import YangMills.Construction.ClusterExpansionOfAStep.ComparisonOfTwoGases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace YangMills.Construction.Dobrushin
structure PairConstraint.OscillationControlled {I : Type} [Fintype I] [DecidableEq I] {S : I → Type}
    [∀ i, MeasurableSpace (S i)] (A : PairConstraint S) (w : I → ℝ) (Kc : ℝ) (F : (∀ i, S i) → ℝ) : Prop where
  nonneg : 0 ≤ Kc
  measurable : Measurable F
  bounded : ∃ C, ∀ σ, |F σ| ≤ C
  oscillation : A.OscillationBound F fun i => Kc * w i
open Classical in
def oscillationComparisonStatement : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (m : ∀ i, Measure (S i)) [∀ i, SigmaFinite (m i)] (G : (∀ i, S i) → ℝ) (z : I → ℝ) (c : I → I → ℝ) (w : I → ℝ)
    (Kc : ℝ) (F : (∀ i, S i) → ℝ) (hG : A.IsActivityBounded m G z),
    A.HasDobrushinColumns m hG.measurable_weightDensity c w → A.OscillationControlled w Kc F →
    |∫ σ, F σ ∂A.gibbsLaw m G - F A.vacant| ≤ Kc * (4 * ∑ i, w i * z i)) ∧
  ∀ (I₁ I₂ J : Type) [Fintype I₁] [DecidableEq I₁] [Fintype I₂] [DecidableEq I₂] [Fintype J] [DecidableEq J]
    (S₁ : I₁ → Type) (S₂ : I₂ → Type) (T : J → Type) [∀ i, MeasurableSpace (S₁ i)] [∀ i, MeasurableSpace (S₂ i)]
    [∀ j, MeasurableSpace (T j)]
    (A₁ : PairConstraint S₁) (A₂ : PairConstraint S₂) (A : PairConstraint T)
    (m₁ m₁' : ∀ i, Measure (S₁ i)) (m₂ m₂' : ∀ i, Measure (S₂ i)) (μ : ∀ j, Measure (T j))
    [∀ i, SigmaFinite (m₁ i)] [∀ i, SigmaFinite (m₁' i)] [∀ i, SigmaFinite (m₂ i)] [∀ i, SigmaFinite (m₂' i)]
    [∀ j, SigmaFinite (μ j)]
    (G₁ : (∀ i, S₁ i) → ℝ) (G₂ : (∀ i, S₂ i) → ℝ) (z₁ : I₁ → ℝ) (z₂ : I₂ → ℝ)
    (e₁ : J → I₁) (e₂ : J → I₂) (v₁ : ∀ j, T j ≃ᵐ S₁ (e₁ j)) (v₂ : ∀ j, T j ≃ᵐ S₂ (e₂ j))
    (c₁ : I₁ → I₁ → ℝ) (c₂ : I₂ → I₂ → ℝ) (w₁ : I₁ → ℝ) (w₂ : I₂ → ℝ) (b E D : J → ℝ) (Kc : ℝ)
    (H₁ : Finset I₁) (H₂ : Finset I₂) (F₁ : (∀ i, S₁ i) → ℝ) (F₂ : (∀ i, S₂ i) → ℝ)
    (hG₁ : A₁.IsActivityBounded m₁ G₁ z₁) (hG₂ : A₂.IsActivityBounded m₂ G₂ z₂),
    Function.Injective e₁ → Function.Injective e₂ → A₁.IsVacantOffRange m₁ m₁' e₁ → A₂.IsVacantOffRange m₂ m₂' e₂ →
    (∀ i ∈ H₁, m₁ i = Measure.dirac (A₁.vacant i)) → (∀ i ∈ H₂, m₂ i = Measure.dirac (A₂.vacant i)) →
    (∀ j, v₁ j (A.vacant j) = A₁.vacant (e₁ j)) → (∀ j, v₂ j (A.vacant j) = A₂.vacant (e₂ j)) →
    (∀ j j' s t, j ≠ j' → (A.compatible j j' s t ↔ A₁.compatible (e₁ j) (e₁ j') (v₁ j s) (v₁ j' t))) →
    (∀ j j' s t, j ≠ j' → (A.compatible j j' s t ↔ A₂.compatible (e₂ j) (e₂ j') (v₂ j s) (v₂ j' t))) →
    (∀ j, MeasurePreserving (v₁ j) (μ j) (m₁ (e₁ j))) → (∀ j, MeasurePreserving (v₂ j) (μ j) (m₂ (e₂ j))) →
    A₁.HasDobrushinColumns m₁ hG₁.measurable_weightDensity c₁ w₁ →
    A₂.HasDobrushinColumns m₂ hG₂.measurable_weightDensity c₂ w₂ →
    A₁.OscillationControlled w₁ Kc F₁ → A₂.OscillationControlled w₂ Kc F₂ →
    (∀ j, 0 ≤ D j) →
    (∀ τ, A.IsAdmissible τ → |F₁ (A₁.embedConfig e₁ (fun j => v₁ j) τ) - F₂ (A₂.embedConfig e₂ (fun j => v₂ j) τ)| ≤
      ∑ j, if τ j = A.vacant j then 0 else D j) →
    (∀ j, 0 ≤ b j) →
    (∀ j, 2 * (z₁ (e₁ j) + z₂ (e₂ j)) ≤ b j ∨
      (1 ≤ E j ∧ z₁ (e₁ j) ≤ 1 ∧ z₂ (e₂ j) ≤ 1 ∧ 8 * (E j - 1) * max (z₁ (e₁ j)) (z₂ (e₂ j)) ≤ b j ∧
        ∀ τ s, A.IsAdmissible (Function.update τ j s) →
          G₁ (A₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j s)) *
              G₂ (A₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j (A.vacant j))) ≤
            E j * (G₁ (A₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j (A.vacant j))) *
              G₂ (A₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j s))) ∧
          G₂ (A₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j s)) *
              G₁ (A₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j (A.vacant j))) ≤
            E j * (G₂ (A₂.embedConfig e₂ (fun j => v₂ j) (Function.update τ j (A.vacant j))) *
              G₁ (A₁.embedConfig e₁ (fun j => v₁ j) (Function.update τ j s))))) →
    |∫ σ, F₁ σ ∂A₁.gibbsLaw m₁ G₁ - ∫ σ, F₂ σ ∂A₂.gibbsLaw m₂ G₂| ≤
      Kc * (4 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e₁ j ≠ i) ∧ i ∉ H₁), w₁ i * z₁ i +
        4 * ∑ i ∈ Finset.univ.filter (fun i => (∀ j, e₂ j ≠ i) ∧ i ∉ H₂), w₂ i * z₂ i +
        2 * ∑ j, w₁ (e₁ j) * b j) + ∑ j, D j * z₂ (e₂ j)
end YangMills.Construction.Dobrushin
end
