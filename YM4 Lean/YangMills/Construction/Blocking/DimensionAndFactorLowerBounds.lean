import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.Blocking
structure DimensionAndFactorLowerBounds (d L : ℕ) : Prop where
  two_le_dim : 2 ≤ d
  two_le_factor : 2 ≤ L
end YangMills.Construction.Blocking
