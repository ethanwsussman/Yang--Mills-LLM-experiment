import YangMills.Construction.Matrices.HaarExpChartDensity
import YangMills.Construction.Thresholds.DegreeFunctions
import Mathlib
open MeasureTheory
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
structure IsGaugeFixingCeiling (A₀ : ℝ) (𝔭₀ : ℕ) (r ε b γ : ℝ) : Prop where
  radius_pos : 0 < r
  radius_le : r ≤ Real.pi / Real.sqrt 2
  density_bounds : ∀ Y : LieElement, operatorNorm Y.toMatrix < r →
    1 / 2 * haarChartDensity ≤ haarExpDensity Y.toMatrix ∧
      haarExpDensity Y.toMatrix ≤ 2 * haarChartDensity
  threshold_pos : 0 < ε
  ball_in_chart : ∀ u : specialUnitary, operatorNorm ((u : ComplexMatrix2) - 1) < ε →
    ∃ Y : LieElement, operatorNorm Y.toMatrix < r ∧
      matExp (Complex.I • Y.toMatrix) = (u : ComplexMatrix2)
  exp_sub_one_le : ∀ Y : LieElement,
    operatorNorm (matExp (Complex.I • Y.toMatrix) - 1) ≤ b * operatorNorm Y.toMatrix
  ceiling_pos : 0 < γ
  ceiling_lt : γ < min 1 r
  threshold_le : ∀ t : ℝ, 0 < t → t ≤ γ →
    t * YangMills.Construction.Thresholds.degreeZero A₀ 𝔭₀ t ≤ ε
  degree_gt : ∀ t : ℝ, 0 < t → t ≤ γ →
    b < YangMills.Construction.Thresholds.degreeZero A₀ 𝔭₀ t
end YangMills.Construction.Matrices.ComplexMatrix2
