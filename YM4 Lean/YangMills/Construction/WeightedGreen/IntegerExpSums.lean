import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedGreen
def intExpSum (κ : ℝ) : ℝ :=
  ∑' n : ℤ, Real.exp (-κ * |(n : ℝ)|)
def blockSumConst (d L : ℕ) (κ : ℝ) : ℝ :=
  15 * Real.exp (1 / 2 * κ * (d : ℝ) * ((L : ℝ) + 3)) * intExpSum (1 / 2 * κ) ^ (3 * d)
end WeightedGreen
end YangMills.Construction
