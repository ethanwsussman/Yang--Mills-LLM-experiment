import YangMills.Construction.OneLoopLaw.SignsOfTheAxialCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopLaw.AxialBranchSetting
variable (D : AxialBranchSetting) (i : ℕ) (W : D.Edge (i + 1) → Matrices.ComplexMatrix2)
def chartBase : D.Edge i → Matrices.ComplexMatrix2 := D.branchLift i W
end YangMills.Construction.OneLoopLaw.AxialBranchSetting
end
