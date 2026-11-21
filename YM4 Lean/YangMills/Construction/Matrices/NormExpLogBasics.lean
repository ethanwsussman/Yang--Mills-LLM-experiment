import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
def NormExpLogBasics : Prop :=
  ((∀ X Y : ComplexMatrix2, operatorNorm (X * Y) ≤ operatorNorm X * operatorNorm Y) ∧
    operatorNorm 1 = 1 ∧
    (∀ X : ComplexMatrix2, operatorNorm X.conjTranspose = operatorNorm X) ∧
    (∀ X u v : ComplexMatrix2, u ∈ Matrix.unitaryGroup (Fin 2) ℂ → v ∈ Matrix.unitaryGroup (Fin 2) ℂ →
      operatorNorm (u * X * v) = operatorNorm X) ∧
    (∀ (X : ComplexMatrix2) (i j : Fin 2), ‖X i j‖ ≤ operatorNorm X) ∧
    (∀ (X : ComplexMatrix2) (μ : ℂ) (v : Fin 2 → ℂ), v ≠ 0 → X.mulVec v = μ • v → ‖μ‖ ≤ operatorNorm X) ∧
    (∀ X : ComplexMatrix2, ‖fullTrace X‖ ≤ 2 * operatorNorm X) ∧
    (∀ X : ComplexMatrix2, operatorNorm X ≤ 2 * ⨆ p : Fin 2 × Fin 2, ‖X p.1 p.2‖) ∧
    (∀ X Y : ComplexMatrix2, dist X Y = operatorNorm (X - Y)) ∧
    (∀ S : Set ComplexMatrix2, IsClosed S → IsComplete S)) ∧
  (∀ Z : ComplexMatrix2,
    Summable (fun n : ℕ => ‖((n.factorial : ℂ)⁻¹) • Z ^ n‖) ∧
    HasSum (fun n : ℕ => ((n.factorial : ℂ)⁻¹) • Z ^ n) (matExp Z) ∧
    matExp Z * matExp (-Z) = 1 ∧
    IsUnit (matExp Z) ∧
    (matExp Z)⁻¹ = matExp (-Z) ∧
    (matExp Z).conjTranspose = matExp Z.conjTranspose ∧
    ∀ W : ComplexMatrix2, IsUnit W → W * matExp Z * W⁻¹ = matExp (W * Z * W⁻¹)) ∧
  (∀ X W : ComplexMatrix2, operatorNorm (X - 1) < 1 → W ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (W * X * W⁻¹ - 1) = operatorNorm (X - 1) ∧ logSeries (W * X * W⁻¹) = W * logSeries X * W⁻¹) ∧
  {A : ComplexMatrix2 | ∃ B ∈ hermitianTraceless, ∃ C ∈ hermitianTraceless, A = B + Complex.I • C} =
    {A : ComplexMatrix2 | fullTrace A = 0}
end YangMills.Construction.Matrices.ComplexMatrix2
