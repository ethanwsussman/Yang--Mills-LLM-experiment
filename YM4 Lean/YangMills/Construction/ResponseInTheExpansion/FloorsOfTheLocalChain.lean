import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
structure LocalChainFloors (K c x : ℝ) : Prop where
  one_le : 1 ≤ x
  one_le_scale : 1 ≤ (⌊Real.log x ^ 3⌋₊ : ℝ)
  one_le_depth : 1 ≤ ⌊Real.log x ^ 2⌋₊
  radii_le : 20 * x ^ ((1 : ℝ) / 90) + 4 * (⌊Real.log x ^ 3⌋₊ : ℝ) + 4 ≤ (⌊x ^ ((1 : ℝ) / 20)⌋₊ : ℝ) / 8
  le_two_pow_depth : x ≤ 2 ^ ⌊Real.log x ^ 2⌋₊
  rpow_le_self : 20 * x ^ ((1 : ℝ) / 90) ≤ x
  card_le : K * x ^ ((1 : ℝ) / 5) ≤ x
  exp_le : Real.exp (-(c * (⌊Real.log x ^ 3⌋₊ : ℝ))) ≤ x ^ (-2 : ℝ)
  inv_le : K * x ^ (-1 : ℝ) ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000)
  logs_le : (⌊Real.log x ^ 3⌋₊ : ℝ) + (⌊Real.log x ^ 2⌋₊ : ℝ) + 4 ≤ x ^ ((1 : ℝ) / 1000)
  depth_inv_sq_le : K * (⌊Real.log x ^ 2⌋₊ : ℝ) * x ^ (-2 : ℝ) ≤ x ^ (-(1 / 2 : ℝ) + 1 / 1000)
def localChainFloorsStatement : Prop :=
  ∀ K c : ℝ, 0 ≤ K → 0 < c → ∀ᶠ x : ℝ in Filter.atTop, LocalChainFloors K c x
end ResponseInTheExpansion
end YangMills.Construction
end
