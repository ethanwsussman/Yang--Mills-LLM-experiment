import YangMills.Construction.Towers.AveragingMapNearTheTrivialConfiguration
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace Tower
def smoothingStepConstant (L : ℕ) : ℝ :=
  (12 * (L : ℝ) ^ 3 + 2) * (2560 * (polydiscRadius L)⁻¹ ^ 2)
end Tower
end YangMills.Construction
end
