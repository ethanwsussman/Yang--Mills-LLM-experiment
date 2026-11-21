import YangMills.Construction.Dirichlet.GreenOperatorEstimates
import YangMills.Construction.Weighted.InverseExpansionConstants
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Weighted
def projDecayRate (d L : ℕ) : ℝ :=
  1 / 8 * min (YangMills.Construction.DirichletGreen.FourDimensional.decayRate L)
    (expansionDecayRate d L)
def projBlockFloor (L : ℕ) : ℝ := YangMills.Construction.DirichletGreen.FourDimensional.blockFloor L
def projSeparationFloor (d L : ℕ) : ℝ :=
  max (YangMills.Construction.DirichletGreen.FourDimensional.gapFloor L)
    (max (expansionSeparationFloor d L)
      (2 * ((d : ℝ) + 2) * (Real.log (L : ℝ) + 1) / projDecayRate d L))
def projBoundConst (d L : ℕ) : ℝ :=
  2 / lowerBoundConst d * YangMills.Construction.DirichletGreen.FourDimensional.boundConstant L ^ 2 *
    (L : ℝ) ^ (d + 4) * latticeSumConst d L (projDecayRate d L) ^ 2
end YangMills.Construction.Weighted
