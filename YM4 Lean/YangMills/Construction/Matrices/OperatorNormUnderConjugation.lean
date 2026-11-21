import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices
namespace ComplexMatrix2
def OperatorNormUnderConjugation : Prop :=
  (∀ X u v : ComplexMatrix2, u ∈ Matrix.unitaryGroup (Fin 2) ℂ → v ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (u * X * v) = operatorNorm X) ∧
  (∀ X V : ComplexMatrix2, V ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (V * X * V⁻¹) = operatorNorm X) ∧
  (∀ V : ComplexMatrix2, V ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (V⁻¹ - 1) = operatorNorm (V - 1)) ∧
  (∀ V W : ComplexMatrix2, V ∈ Matrix.unitaryGroup (Fin 2) ℂ → W ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (V * W⁻¹ - 1) = operatorNorm (V - W)) ∧
  (∀ T Z : ComplexMatrix2, IsUnit T → T * matExp Z * T⁻¹ = matExp (T * Z * T⁻¹)) ∧
  (∀ T X : ComplexMatrix2, IsUnit T → operatorNorm (X - 1) < 1 →
    operatorNorm (T * X * T⁻¹ - 1) < 1 →
    logSeries (T * X * T⁻¹) = T * logSeries X * T⁻¹) ∧
  (∀ T X : ComplexMatrix2, T ∈ Matrix.unitaryGroup (Fin 2) ℂ → operatorNorm (X - 1) < 1 →
    operatorNorm (T * X * T⁻¹ - 1) < 1)
end ComplexMatrix2
end YangMills.Construction.Matrices
