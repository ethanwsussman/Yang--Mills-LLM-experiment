import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ScaledVariables
def HaarGapTailSmooth : Prop :=
  ∃ h : ℝ → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h ∧ (∀ u, 0 ≤ u → 0 < h u) ∧
    ∀ u, 0 ≤ u → haarGapTail u = -Real.log (h u)
end YangMills.Construction.ScaledVariables
end
