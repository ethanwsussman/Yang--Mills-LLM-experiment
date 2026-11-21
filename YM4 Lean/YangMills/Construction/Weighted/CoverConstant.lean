import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def coverConst (d L : ℕ) : ℝ :=
  max (9 / 2 * Real.pi * (L : ℝ)) (2 ^ (d + 1))
end YangMills.Construction.Weighted
