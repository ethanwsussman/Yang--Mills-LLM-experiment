import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Blocking
structure FourDimOddFactor (d L : ℕ) : Prop where
  dim_eq_four : d = 4
  three_le_factor : 3 ≤ L
  factor_odd : Odd L
end YangMills.Construction.Blocking
