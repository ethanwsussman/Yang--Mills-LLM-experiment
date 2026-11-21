import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RealPower
def rpowPos (x t : ℝ) : ℝ :=
  if 0 < x then Real.exp (t * Real.log x) else 0
def sqrtOf (x : ℝ) : ℝ :=
  if x = 0 then 0 else rpowPos x (1 / 2)
def cbrtOf (x : ℝ) : ℝ :=
  rpowPos x (1 / 3)
end YangMills.Construction.RealPower
end
