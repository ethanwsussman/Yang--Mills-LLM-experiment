import YangMills.Construction.SystemOfAdmissibleConstants.NumbersOfTheSystem
import YangMills.Construction.WindowAtItsEnds.FourBoundsWithTheTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
open YangMills.Construction.CouplingFlow
def constantFamiliesOfBounds (L : ℕ) (A b : ℝ) : ConstantFamilies where
  torusConst := cumulantBound L A b
  supConst := cumulantBound L A b
  starConst := cumulantBound L A b
  onePointConst := onePointBound L A b
end YangMills.Construction.AdmissibleConstants
end
