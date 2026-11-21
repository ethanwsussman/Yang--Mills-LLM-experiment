import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace HullsInEveryVolume
def dyadicDiameterFloor (r i : ℕ) : ℝ := if i = 0 then 0 else 2 ^ (i - 1) * (r : ℝ)
def holderExponentAtBand (L r i : ℕ) : ℕ := ⌈((L : ℝ) * (16 * (2 ^ i * (r : ℝ)) + 40 * (r : ℝ))) ^ 4⌉₊
end HullsInEveryVolume
end YangMills.Construction
end
