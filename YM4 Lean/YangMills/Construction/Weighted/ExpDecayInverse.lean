import YangMills.Construction.Weighted.GivenChain
import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def decayRateOfInverse (L : ℕ) (γ κ C : ℝ) : ℝ :=
  min (κ / 4) (Real.exp 1 * γ * κ / (8 * C * latticeSumConst 4 L (κ / 2)))
end YangMills.Construction.Weighted
