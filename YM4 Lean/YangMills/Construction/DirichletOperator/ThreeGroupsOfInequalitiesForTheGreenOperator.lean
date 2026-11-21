import YangMills.Construction.Dirichlet.SecondDifferenceConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.GreenThreeGroups
def weightLower (L : ℕ) : ℝ := 1 - ((L : ℝ) ^ 2)⁻¹
def pointwiseConst (L : ℕ) (ε : ℝ) : ℝ :=
  Dirichlet.SecondDifference.pointwiseBoundConst 4 L (weightLower L) 1 ε
def holderConst (L : ℕ) (ε β₀ : ℝ) : ℝ :=
  Dirichlet.SecondDifference.holderBoundConst 4 L (weightLower L) 1 ε β₀
def secondDiffBound (L : ℕ) : ℝ :=
  Dirichlet.SecondDifference.secondDiffConst 4 L (weightLower L) 1
end YangMills.Construction.GreenThreeGroups
end
