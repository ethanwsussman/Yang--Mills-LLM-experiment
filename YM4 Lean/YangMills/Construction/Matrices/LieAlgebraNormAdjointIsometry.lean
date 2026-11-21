import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
def LieAlgebraNormAdjointIsometry : Prop :=
  (∀ X : LieElement, halfTrace (X.toMatrix * X.toMatrix) = ((operatorNorm X.toMatrix ^ 2 : ℝ) : ℂ)) ∧
  (∀ X Y : LieElement, halfTrace (X.toMatrix * Y.toMatrix) = ((inner ℝ X Y : ℝ) : ℂ)) ∧
  (∀ X : LieElement, ‖X‖ = operatorNorm X.toMatrix) ∧
  (∀ X Y : LieElement, |inner ℝ X Y| ≤ operatorNorm X.toMatrix * operatorNorm Y.toMatrix) ∧
  (∀ T : LieElement →ₗ[ℝ] LieElement,
    ‖LinearMap.toContinuousLinearMap (LinearMap.adjoint T)‖ =
      ‖LinearMap.toContinuousLinearMap T‖) ∧
  (∀ g ∈ specialUnitary, ∀ Y : ComplexMatrix2, operatorNorm (conjugateBy g Y) = operatorNorm Y) ∧
  (∀ g ∈ specialUnitary,
    conjugateBy g '' (hermitianTraceless : Set ComplexMatrix2) = (hermitianTraceless : Set ComplexMatrix2)) ∧
  (∀ g ∈ specialUnitary, ∀ X ∈ hermitianTraceless, ∀ Y ∈ hermitianTraceless,
    halfTrace (conjugateBy g X * conjugateBy g Y) = halfTrace (X * Y)) ∧
  (∀ g ∈ specialUnitary, ∀ s : ℝ, (s = 1 ∨ s = -1) →
    ∃ R : LieElement ≃ₗᵢ[ℝ] LieElement, ∀ X : LieElement,
      (R X).toMatrix = s • conjugateBy g X.toMatrix) ∧
  (∀ g ∈ specialUnitary, ∀ g' ∈ specialUnitary, ∀ Y : ComplexMatrix2,
    operatorNorm (conjugateBy g Y - conjugateBy g' Y) ≤ 2 * operatorNorm (g - g') * operatorNorm Y)
end YangMills.Construction.Matrices.ComplexMatrix2
