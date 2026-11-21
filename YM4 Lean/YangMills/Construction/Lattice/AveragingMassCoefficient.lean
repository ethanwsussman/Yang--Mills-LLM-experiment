import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Lattice
def averagingMassCoefficient (L : ℕ) : ℕ → ℝ
  | 0 => 1
  | 1 => 1
  | j + 2 => averagingMassCoefficient L (j + 1) /
      ((L : ℝ) ^ (-2 : ℤ) + averagingMassCoefficient L (j + 1))
end YangMills.Construction.Lattice
