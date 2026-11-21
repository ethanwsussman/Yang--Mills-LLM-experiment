import YangMills.Construction.Averaging.SingleStepConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Averaging.Pinch
def corridorConstant (L : ℕ) : ℝ :=
  2 * Averaging.SingleStep.loopAngleConstant L + Averaging.SingleStep.loopVariableConstant L +
    Averaging.SingleStep.meanLogConstant L
def holonomyConstant (L : ℕ) : ℝ :=
  2 * (corridorConstant L + Averaging.SingleStep.loopAngleConstant L)
end YangMills.Construction.Averaging.Pinch
end
