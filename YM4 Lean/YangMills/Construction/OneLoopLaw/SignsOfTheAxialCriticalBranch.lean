import YangMills.Construction.OneLoopLaw.TheAxialCriticalBranch
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace OneLoopLaw
namespace AxialBranchSetting
variable (D : AxialBranchSetting)
def branchNhd (i : ℕ) : Set (D.Edge i → Matrices.ComplexMatrix2) :=
  D.chosenBranch.nhdAt i
def branchLift (i : ℕ) : (D.Edge (i + 1) → Matrices.ComplexMatrix2) → D.Edge i → Matrices.ComplexMatrix2 :=
  D.chosenBranch.lift i
def branchComp (i : ℕ) : (D.Edge i → Matrices.ComplexMatrix2) → D.Edge 0 → Matrices.ComplexMatrix2 :=
  D.chosenBranch.comp i
end AxialBranchSetting
end OneLoopLaw
end YangMills.Construction
end
