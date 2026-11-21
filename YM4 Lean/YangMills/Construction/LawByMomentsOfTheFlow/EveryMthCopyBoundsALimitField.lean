import YangMills.Construction.LawByMomentsOfTheFlow.LimitFieldOfCopies
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace YangMills.Construction.MomentMethod
def multipleTranslatesBoundStatement : Prop :=
  ∀ (T : TranslatedLaws) (J : Type) [Countable J] (X : J → T.Family) (P : Measure (TranslateValues J)), T.IsPreserving →
    (∀ j, TranslatedLaws.HasBoundedMoments (X j)) → IsJointLimitLaw T X P →
    ∀ (j : J) (b C₀ Cb : ℝ) (m : ℕ), 1 ≤ m → 0 ≤ b → (∀ᵐ v ∂P, 0 ≤ v (j, 0) ∧ v (j, 0) ≤ Cb) →
      (∀ q : ℕ, 1 ≤ q → ∃ gap : ℕ, ∀ k : Fin q → ℕ, (∀ c e, c ≠ e → gap ≤ k c - k e ∨ gap ≤ k e - k c) →
        ∫ v, ∏ c, v (j, m * k c) ∂P ≤ C₀ * b ^ q) →
      ∀ᵐ v ∂P, invariantCondExp P (evalAtZero j) v ≤ b
end YangMills.Construction.MomentMethod
end
