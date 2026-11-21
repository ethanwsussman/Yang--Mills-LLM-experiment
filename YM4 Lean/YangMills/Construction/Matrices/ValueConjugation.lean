import YangMills.Construction.Matrices.SpecialUnitaryTwoNotation
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def algebraConjMatrix (A : ComplexMatrix2) : ComplexMatrix2 := adjointMatrix A
variable {ι κ Ξ : Type*}
def algebraConjPointwise (J : ι → ComplexMatrix2) : ι → ComplexMatrix2 :=
  fun i => algebraConjMatrix (J i)
end YangMills.Construction.Matrices.ComplexMatrix2
