import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SoftAverages
def haarDensity (y : Fin 3 → ℝ) : ℝ :=
  if y = 0 then 1 else (Real.sin (Real.sqrt (∑ i, y i ^ 2)) / Real.sqrt (∑ i, y i ^ 2)) ^ 2
end YangMills.Construction.SoftAverages
end
