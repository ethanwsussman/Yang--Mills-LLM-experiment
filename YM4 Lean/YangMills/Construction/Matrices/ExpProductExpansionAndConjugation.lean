import YangMills.Construction.Matrices.SpecialUnitaryTwo
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def halfCommutatorSum {r : ℕ} (Y : Fin r → ComplexMatrix2) : ComplexMatrix2 :=
  (1 / 2 : ℂ) • ∑ i, ∑ j ∈ Finset.Ioi i, (Y i * Y j - Y j * Y i)
def ExpProductExpansionAndConjugation : Prop :=
  (∀ (r : ℕ) (Y : Fin r → ComplexMatrix2) (σ : ℝ) (s c P : ComplexMatrix2),
    σ = ∑ i, operatorNorm (Y i) → s = ∑ i, Y i → c = halfCommutatorSum Y →
    P = (List.ofFn fun i => matExp (Y i)).prod →
    operatorNorm (P - 1 - s) ≤ Real.exp σ - 1 - σ ∧
    Real.exp σ - 1 - σ ≤ 1 / 2 * σ ^ 2 * Real.exp σ ∧
    operatorNorm (P - 1 - s - (1 / 2 : ℂ) • s ^ 2 - c) ≤ Real.exp σ - 1 - σ - 1 / 2 * σ ^ 2 ∧
    Real.exp σ - 1 - σ - 1 / 2 * σ ^ 2 ≤ 1 / 6 * σ ^ 3 * Real.exp σ) ∧
  (∀ V Y : ComplexMatrix2, operatorNorm (V - 1) ≤ 1 / 4 →
    operatorNorm (V * Y * V⁻¹ - Y) ≤ 3 * operatorNorm (V - 1) * operatorNorm Y) ∧
  (∀ Z Y : ComplexMatrix2,
    operatorNorm (matExp Z * Y * matExp (-Z) - Y) ≤
      (Real.exp (2 * operatorNorm Z) - 1) * operatorNorm Y)
end YangMills.Construction.Matrices.ComplexMatrix2
