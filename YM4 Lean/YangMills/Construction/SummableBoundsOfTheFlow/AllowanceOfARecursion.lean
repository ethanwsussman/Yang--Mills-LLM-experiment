import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CouplingFlow
def AllowanceOfRecursionHolds : Prop :=
  ∀ (b d : ℕ → ℝ) (c₀ c M R y₀ : ℝ), 0 < c₀ → 0 ≤ M → 0 ≤ R → (∀ l, |d l| ≤ M) → HasAverageSlope b c₀ c →
    ∃ (X C v₀ : ℝ) (w : ℕ), y₀ ≤ X ∧ 8 ≤ X ∧ 0 ≤ C ∧ 8 * C * X ^ (-(1 / 4) : ℝ) ≤ 1 ∧ 1 ≤ w ∧ X + 1 ≤ v₀ ∧
      FlowAbove b d X v₀ ∧
      ∀ x : ℕ → ℝ, FollowsFlowAbove b d R X x → FlowBounds b d c₀ c M R X C w v₀ x
end YangMills.Construction.CouplingFlow
end
