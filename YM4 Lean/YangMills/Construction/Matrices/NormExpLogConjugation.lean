import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
namespace YangMills.Construction.Matrices.ComplexMatrix2
def NormExpLogConjugation : Prop :=
  (∀ X Z : ComplexMatrix2, operatorNorm (X * Z) ≤ operatorNorm X * operatorNorm Z) ∧
  operatorNorm (1 : ComplexMatrix2) = 1 ∧
  (∀ X u v : ComplexMatrix2, u ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    v ∈ Matrix.unitaryGroup (Fin 2) ℂ → operatorNorm (u * X * v) = operatorNorm X) ∧
  (∀ X g : ComplexMatrix2, g ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (g * X * g⁻¹ - 1) = operatorNorm (X - 1)) ∧
  (∀ V : ComplexMatrix2, V ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (V⁻¹ - 1) = operatorNorm (V - 1)) ∧
  (∀ g Z : ComplexMatrix2, IsUnit g → matExp (g * Z * g⁻¹) = g * matExp Z * g⁻¹) ∧
  (∀ g X : ComplexMatrix2, IsUnit g → operatorNorm (X - 1) < 1 →
    operatorNorm (g * X * g⁻¹ - 1) < 1 →
    logSeries (g * X * g⁻¹) = g * logSeries X * g⁻¹) ∧
  (∀ g X : ComplexMatrix2, g ∈ Matrix.unitaryGroup (Fin 2) ℂ → operatorNorm (X - 1) < 1 →
    operatorNorm (g * X * g⁻¹ - 1) < 1)
end YangMills.Construction.Matrices.ComplexMatrix2
