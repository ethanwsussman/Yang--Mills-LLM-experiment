import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
def ExpImaginaryLieMem : Prop :=
  (∀ Y ∈ hermitianTraceless, matExp (Complex.I • Y) ∈ specialUnitary) ∧
  ∀ A ∈ traceless, matExp (Complex.I • A) ∈ unitDeterminant
end YangMills.Construction.Matrices.ComplexMatrix2
