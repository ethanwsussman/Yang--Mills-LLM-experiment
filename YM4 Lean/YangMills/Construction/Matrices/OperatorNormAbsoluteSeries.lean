import YangMills.Construction.Matrices.MatrixSeries
import Mathlib
open Filter
open scoped Matrix.Norms.L2Operator Topology
noncomputable section
namespace YangMills.Construction.Matrices.ComplexMatrix2
def maxEntryNorm (X : ComplexMatrix2) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun p : Fin 2 × Fin 2 => ‖X p.1 p.2‖)
def OperatorNormSeriesProperties : Prop :=
  (∀ X : ComplexMatrix2, maxEntryNorm X ≤ operatorNorm X ∧ operatorNorm X ≤ 2 * maxEntryNorm X) ∧
  (∀ X : ComplexMatrix2, BddAbove
    ((fun v : EuclideanSpace ℂ (Fin 2) => coordinateNorm (Matrix.toEuclideanLin X v)) ''
      Metric.sphere 0 1)) ∧
  (∀ X : ComplexMatrix2, operatorNorm X = 0 → X = 0) ∧
  (∀ (X : ComplexMatrix2) (v : EuclideanSpace ℂ (Fin 2)),
    coordinateNorm (Matrix.toEuclideanLin X v) ≤ operatorNorm X * coordinateNorm v) ∧
  (∀ (X : ComplexMatrix2) (C : ℝ),
    (∀ v : EuclideanSpace ℂ (Fin 2),
      coordinateNorm (Matrix.toEuclideanLin X v) ≤ C * coordinateNorm v) → operatorNorm X ≤ C) ∧
  (∀ X Y : ComplexMatrix2, operatorNorm (X + Y) ≤ operatorNorm X + operatorNorm Y) ∧
  (∀ (c : ℂ) (X : ComplexMatrix2), operatorNorm (c • X) = ‖c‖ * operatorNorm X) ∧
  (∀ X Y : ComplexMatrix2, operatorNorm (X * Y) ≤ operatorNorm X * operatorNorm Y) ∧
  operatorNorm 1 = 1 ∧
  (∀ (X : ComplexMatrix2) (n : ℕ), operatorNorm (X ^ n) ≤ operatorNorm X ^ n) ∧
  (∀ X u w : ComplexMatrix2, u ∈ Matrix.unitaryGroup (Fin 2) ℂ → w ∈ Matrix.unitaryGroup (Fin 2) ℂ →
    operatorNorm (u * X * w) = operatorNorm X) ∧
  (∀ (S : ComplexMatrix2) (T : ℕ → ComplexMatrix2),
    Tendsto (fun k => operatorNorm (S - T k)) atTop (𝓝 0) ↔
      ∀ i j, Tendsto (fun k => T k i j) atTop (𝓝 (S i j))) ∧
  (∀ (T : ℕ → ComplexMatrix2) (S S' : ComplexMatrix2),
    Tendsto (fun k => operatorNorm (S - T k)) atTop (𝓝 0) →
    Tendsto (fun k => operatorNorm (S' - T k)) atTop (𝓝 0) → S = S') ∧
  (∀ (X : ℕ → ComplexMatrix2) (S S' : ComplexMatrix2), HasSeriesSum X S → HasSeriesSum X S' → S = S') ∧
  (∀ X : ℕ → ComplexMatrix2, SeriesAbsolutelyConvergent X →
    SeriesConvergent X ∧
    ∀ S : ComplexMatrix2, HasSeriesSum X S →
      (∀ i j,
        (∃ s : ℝ, Tendsto (fun k => ∑ n ∈ Finset.range (k + 1), ‖X n i j‖) atTop (𝓝 s)) ∧
        Tendsto (fun k => ∑ n ∈ Finset.range (k + 1), X n i j) atTop (𝓝 (S i j))) ∧
      (∀ k : ℕ, operatorNorm (S - seriesPartialSum X k) ≤ ∑' n : ℕ, operatorNorm (X (n + (k + 1)))) ∧
      operatorNorm S ≤ ∑' n : ℕ, operatorNorm (X n)) ∧
  (∀ W : ComplexMatrix2, IsUnit W →
    IsLinearMap ℂ (fun Y : ComplexMatrix2 => W * Y * W⁻¹) ∧
    (∀ Y : ComplexMatrix2, operatorNorm (W * Y * W⁻¹) ≤ operatorNorm W * operatorNorm W⁻¹ * operatorNorm Y) ∧
    ∀ (S : ComplexMatrix2) (T : ℕ → ComplexMatrix2),
      Tendsto (fun k => operatorNorm (S - T k)) atTop (𝓝 0) →
      Tendsto (fun k => operatorNorm (W * S * W⁻¹ - W * T k * W⁻¹)) atTop (𝓝 0))
end YangMills.Construction.Matrices.ComplexMatrix2
