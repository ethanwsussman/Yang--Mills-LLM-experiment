import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def ConjugationExpProductBounds : Prop :=
  (∃ h : Fin 4 → ComplexMatrix2, (∀ k, h k ∈ specialUnitary) ∧
    ∀ Y ∈ traceless, ∑ k, conjugateBy (h k) Y = 0) ∧
  (∀ h ∈ specialUnitary, ∀ Y : ComplexMatrix2,
    operatorNorm (conjugateBy h Y) = operatorNorm Y ∧
    matExp (conjugateBy h Y) = conjugateBy h (matExp Y) ∧
    (Y ∈ traceless → conjugateBy h Y ∈ traceless) ∧
    (Y ∈ hermitianTraceless → conjugateBy h Y ∈ hermitianTraceless)) ∧
  (∀ Y ∈ hermitianTraceless, matExp (Complex.I • Y) ∈ specialUnitary) ∧
  (∀ (A B C : ComplexMatrix2) (q : ℝ), A ∈ hermitianTraceless → B ∈ hermitianTraceless →
    C ∈ hermitianTraceless → operatorNorm A ≤ q → operatorNorm B ≤ q →
    operatorNorm C ≤ q → q ≤ 1 / 12 →
    ∃ Y ∈ hermitianTraceless, matExp (Complex.I • Y) =
        matExp (Complex.I • A) * matExp (Complex.I • B) * matExp (Complex.I • C) ∧
      operatorNorm (Y - (A + B + C)) ≤ 81 * q ^ 2) ∧
  (∀ (A J : ComplexMatrix2) (q : ℝ), A ∈ hermitianTraceless → operatorNorm A ≤ q → q ≤ 1 →
    operatorNorm (conjugateBy (matExp (Complex.I • A)) J - J) ≤ 4 * q * operatorNorm J) ∧
  (∀ (Z₁ Z₂ Z₃ Z₄ : ComplexMatrix2) (r : ℝ), operatorNorm Z₁ ≤ r → operatorNorm Z₂ ≤ r →
    operatorNorm Z₃ ≤ r → operatorNorm Z₄ ≤ r → 4 * r ≤ 1 →
    operatorNorm (matExp Z₁ * matExp Z₂ * matExp Z₃ * matExp Z₄ - 1) ≤ 8 * r)
end YangMills.Construction.Matrices.ComplexMatrix2
end
