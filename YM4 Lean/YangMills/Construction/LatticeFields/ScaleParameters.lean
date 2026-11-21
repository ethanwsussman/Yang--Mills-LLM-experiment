import YangMills.Construction.LatticeFields.FieldsAndDifferences
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFields
structure ScaleData where
  d : ℕ
  L : ℕ
  a : ℝ
  k : ℕ
  two_le_d : 2 ≤ d
  two_le_L : 2 ≤ L
  a_pos : 0 < a
namespace ScaleData
variable (S : ScaleData)
def N : ℕ := S.L ^ S.k
def η : ℝ := latticeSpacing S.N
instance neZeroN : NeZero S.N :=
  ⟨pow_ne_zero _ (by have := S.two_le_L; omega)⟩
end ScaleData
end YangMills.Construction.LatticeFields
