import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Averaging.SingleStep
def loopAngleConstant (L : ℕ) : ℝ := Real.pi / Real.sqrt 3 * ((L : ℝ) - 1) ^ 2
def loopVariableConstant (L : ℕ) : ℝ :=
  3 * (L : ℝ) * ((L : ℝ) - 1) + 2 * loopAngleConstant L
def meanLogConstant (L : ℕ) : ℝ := Real.pi / 2 * loopVariableConstant L
end YangMills.Construction.Averaging.SingleStep
end
