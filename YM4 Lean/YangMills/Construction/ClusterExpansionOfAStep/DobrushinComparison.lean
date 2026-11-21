import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace Dobrushin
variable {I : Type} [Fintype I] [DecidableEq I] {S : I → Type} [∀ i, MeasurableSpace (S i)]
structure PairConstraint (S : I → Type) where
  vacant : ∀ i, S i
  compatible : ∀ i j, S i → S j → Prop
  compatible_symm : ∀ i j (s : S i) (t : S j), compatible i j s t → compatible j i t s
  vacant_compatible : ∀ i j (t : S j), compatible i j (vacant i) t
def PairConstraint.IsAdmissible (A : PairConstraint S) (σ : ∀ i, S i) : Prop :=
  ∀ i j, i ≠ j → A.compatible i j (σ i) (σ j)
def PairConstraint.OscillationBound (A : PairConstraint S) (F : (∀ i, S i) → ℝ) (o : I → ℝ) : Prop :=
  (∀ i, 0 ≤ o i) ∧ ∀ i σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ j, j ≠ i → σ j = σ' j) →
    |F σ - F σ'| ≤ o i
structure PairConstraint.IsSpecification (A : PairConstraint S) (μ : Measure (∀ i, S i))
    (K : ∀ i, Kernel (∀ j, S j) (S i)) : Prop where
  isMarkovKernel : ∀ i, IsMarkovKernel (K i)
  update_eq : ∀ i σ s, K i (Function.update σ i s) = K i σ
  integral_eq : ∀ i (F : (∀ j, S j) → ℝ), Measurable F → (∃ C, ∀ σ, |F σ| ≤ C) →
    ∫ σ, F σ ∂μ = ∫ σ, (∫ s, F (Function.update σ i s) ∂(K i σ)) ∂μ
  ae_admissible_update : ∀ i σ, A.IsAdmissible σ → ∀ᵐ s ∂(K i σ), A.IsAdmissible (Function.update σ i s)
  ae_admissible : ∀ᵐ σ ∂μ, A.IsAdmissible σ
def ComparisonStatement : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (S : I → Type) [∀ i, MeasurableSpace (S i)] (A : PairConstraint S)
    (μ μ' : Measure (∀ i, S i)) [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (K K' : ∀ i, Kernel (∀ j, S j) (S i)) (c : I → I → ℝ) (b w : I → ℝ),
    MeasurableSet {σ | A.IsAdmissible σ} → A.IsSpecification μ K → A.IsSpecification μ' K' →
    (∀ i j, 0 ≤ c i j) → (∀ i, 0 ≤ b i) → (∀ i, 0 < w i) →
    (∀ i j, i ≠ j → ∀ σ σ', A.IsAdmissible σ → A.IsAdmissible σ' → (∀ k, k ≠ j → σ k = σ' k) →
      ∀ B, MeasurableSet B → (K i σ).real B ≤ (K i σ').real B + c i j / 2) →
    (∀ i σ, A.IsAdmissible σ → ∀ B, MeasurableSet B →
      (K i σ).real B ≤ (K' i σ).real B + b i / 2) →
    (∀ j, ∑ i, w i * c i j ≤ w j / 2) →
    ∃ a : I → ℝ, (∀ i, 0 ≤ a i) ∧ ∑ i, w i * a i ≤ 2 * ∑ i, w i * b i ∧
      ∀ (F : (∀ i, S i) → ℝ) (o : I → ℝ), Measurable F → (∃ C, ∀ σ, |F σ| ≤ C) → A.OscillationBound F o →
        |∫ σ, F σ ∂μ - ∫ σ, F σ ∂μ'| ≤ ∑ i, a i * o i
end Dobrushin
end YangMills.Construction
end
