import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingFlow
def TwoSidedDropToNextLevel : Prop :=
  ∀ (b d : ℕ → ℝ) (c₀ c M R : ℝ), 0 < c₀ → 0 ≤ M → 0 ≤ R → (∀ l, |d l| ≤ M) → HasAverageSlope b c₀ c →
    ∃ X₁ : ℝ, ∀ X, X₁ ≤ X → ∀ (x : ℕ → ℝ) (i j : ℕ), i ≤ j → (∀ l < j, X ≤ x l) →
      (∀ l < j, |stepRemainder b d x l| ≤ R * x l ^ (-(5 / 4) : ℝ)) →
      3 / 4 * c₀ * ((j : ℝ) - i) - 2 * c ≤ x i - x j ∧ x i - x j ≤ 5 / 4 * c₀ * ((j : ℝ) - i) + 2 * c
end YangMills.Construction.CouplingFlow
end
