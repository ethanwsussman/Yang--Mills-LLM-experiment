import YangMills.Construction.BackgroundField.NumbersOfTheMinimalOrbitsUnderTheConditionsOfTheOperators
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set PeriodicLattice
open scoped ENNReal
noncomputable section
namespace BackgroundField.PrescribedAverageProblem
def IsSubcriticalExponent (β₀ : ℝ) : Prop := 0 < β₀ ∧ β₀ < 1
def subcriticalB₃AndFloors (L : ℕ) : ℝ × ℝ × ℝ :=
  Classical.epsilon fun T : ℝ × ℝ × ℝ =>
    IsRegularityConstant IsSubcriticalExponent L T.1 T.2.1 T.2.2
def subcriticalB₃ (L : ℕ) : ℝ :=
  if 0 < GreenBoundMinimizers.b₃Const L then
    GreenBoundMinimizers.b₃Const L else 1
def subcriticalProductFloor (L : ℕ) : ℝ := (subcriticalB₃AndFloors L).2.2
end BackgroundField.PrescribedAverageProblem
end
end YangMills.Construction
