import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel
def logConstant (d : ℕ) (ε : ℝ) : ℝ :=
  (d : ℝ) * (1 + Real.log (2 * (d : ℝ))) + ε⁻¹
end YangMills.Construction.FreeKernel
