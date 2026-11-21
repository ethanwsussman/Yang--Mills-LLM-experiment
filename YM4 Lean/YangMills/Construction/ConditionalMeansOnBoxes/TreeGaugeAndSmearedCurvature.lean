import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped Quaternion
noncomputable section
namespace YangMills.Construction.ConditionalMeansOnBoxes
def toQuaternion (V : Matrices.ComplexMatrix2.specialUnitary) : ℍ[ℝ] :=
  ⟨((V : Matrices.ComplexMatrix2) 0 0).re, ((V : Matrices.ComplexMatrix2) 0 0).im,
    ((V : Matrices.ComplexMatrix2) 0 1).re, ((V : Matrices.ComplexMatrix2) 0 1).im⟩
end YangMills.Construction.ConditionalMeansOnBoxes
end
