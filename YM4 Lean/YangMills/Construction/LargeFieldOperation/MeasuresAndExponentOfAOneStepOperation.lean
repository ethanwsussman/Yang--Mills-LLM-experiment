import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open Matrices
namespace LargeField
def lieLebesguePi (ι : Type) : Measure (ι → ComplexMatrix2.LieElement) :=
  open Classical in
  if h : Finite ι then
    letI := @Fintype.ofFinite ι h
    Measure.pi fun _ => ComplexMatrix2.lieLebesgue
  else 0
end LargeField
end YangMills.Construction
end
