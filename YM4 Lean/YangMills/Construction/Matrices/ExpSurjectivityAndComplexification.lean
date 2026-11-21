import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator Pointwise
namespace YangMills.Construction.Matrices.ComplexMatrix2
def ExpSurjectivityAndComplexification : Prop :=
  (∀ Y ∈ hermitianTraceless, matExp (Complex.I • Y) ∈ specialUnitary) ∧
  (∀ g ∈ specialUnitary, ∃ Y ∈ hermitianTraceless, matExp (Complex.I • Y) = g) ∧
  (ConnectedSpace specialUnitary ∧ ∀ (S : Type) [Finite S], ConnectedSpace (S → specialUnitary)) ∧
  hermitianTraceless ⊓ Complex.I • hermitianTraceless = ⊥ ∧
  hermitianTraceless ⊔ Complex.I • hermitianTraceless = traceless.restrictScalars ℝ ∧
  ∀ (ι : Type) (b : Module.Basis ι ℝ hermitianTraceless),
    ∃ c : Module.Basis ι ℂ traceless, ∀ i, (c i : ComplexMatrix2) = (b i : ComplexMatrix2)
end YangMills.Construction.Matrices.ComplexMatrix2
