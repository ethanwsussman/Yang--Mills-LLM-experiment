import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory
namespace YangMills.Construction
namespace Measures
def HaarMapMulInvEq : Prop :=
  ∀ g : Matrices.ComplexMatrix2.specialUnitary,
    Matrices.ComplexMatrix2.haarProb.map
      (fun h : Matrices.ComplexMatrix2.specialUnitary => g * h⁻¹) =
      Matrices.ComplexMatrix2.haarProb
end Measures
end YangMills.Construction
