import YangMills.Construction.Weighted.GreenSquareConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def separatedSumConst (d L : ℕ) (κ : ℝ) : ℝ := latticeSumConst d L κ
def separatedSumRadius (d L : ℕ) (κ : ℝ) : ℝ := latticeSumRadius d L κ
end YangMills.Construction.Weighted
