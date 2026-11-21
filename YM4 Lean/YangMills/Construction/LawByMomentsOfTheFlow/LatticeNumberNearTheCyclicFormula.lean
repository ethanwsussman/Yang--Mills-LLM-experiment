import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open TestFunctions CyclicFormula
def latticeCycleSumApproxStatement : Prop :=
  ∀ (k : ℕ) [NeZero k], 2 ≤ k → ∀ R d : ℝ, 0 ≤ R → 0 < d → ∃ C : ℝ, ∀ (φ : Fin k → EuclideanFourSpace → ℝ) (L s : ℕ), 1 ≤ L →
    IsSupTestFamily R d φ →
    |latticeCycleSum L s (⌈R * (L : ℝ) ^ s⌉₊ + 2) φ| ≤ C ∧
    |latticeCycleSum L s (⌈R * (L : ℝ) ^ s⌉₊ + 2) φ - cyclicMomentFormula k φ| ≤ C * (L : ℝ) ^ (-(s : ℝ))
end YangMills.Construction.MomentLaw
end
