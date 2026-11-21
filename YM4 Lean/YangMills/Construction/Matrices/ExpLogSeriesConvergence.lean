import YangMills.Construction.Matrices.MatrixSeries
import Mathlib
open Filter
open scoped Matrix.Norms.L2Operator Topology
namespace YangMills.Construction.Matrices
namespace ComplexMatrix2
def ExpLogSeriesConvergence : Prop :=
  (∀ Z : ComplexMatrix2,
    SeriesAbsolutelyConvergent (expSeriesTerm Z) ∧
    ∑' n : ℕ, operatorNorm (expSeriesTerm Z n) ≤ Real.exp (operatorNorm Z) ∧
    (∃! S : ComplexMatrix2,
      Tendsto (fun l => operatorNorm (S - expSeriesPartialSum Z l)) atTop (𝓝 0)) ∧
    Tendsto (fun l => operatorNorm (matExp Z - expSeriesPartialSum Z l)) atTop (𝓝 0) ∧
    (∀ i j : Fin 2,
      Summable (fun n : ℕ => ‖(Z ^ n) i j / (n.factorial : ℂ)‖) ∧
      HasSum (fun n : ℕ => (Z ^ n) i j / (n.factorial : ℂ)) (matExp Z i j)) ∧
    (∀ l : ℕ, operatorNorm (matExp Z - expSeriesPartialSum Z l) ≤
      ∑' n : Set.Ioi l, operatorNorm Z ^ (n : ℕ) / ((n : ℕ).factorial : ℝ)) ∧
    operatorNorm (matExp Z - 1) ≤ Real.exp (operatorNorm Z) - 1 ∧
    operatorNorm (matExp Z - 1 - Z) ≤ Real.exp (operatorNorm Z) - 1 - operatorNorm Z ∧
    operatorNorm (matExp Z) ≤ Real.exp (operatorNorm Z)) ∧
  (∀ (X : ComplexMatrix2) (t : ℝ), t = operatorNorm (X - 1) → t < 1 →
    SeriesAbsolutelyConvergent (logSeriesTerm X) ∧
    ∑' n : Set.Ici (1 : ℕ), operatorNorm ((((n : ℕ) : ℂ)⁻¹) • (1 - X) ^ (n : ℕ)) ≤
      -realLog (1 - t) ∧
    (∃! S : ComplexMatrix2,
      Tendsto (fun l => operatorNorm (S - logSeriesPartialSum X l)) atTop (𝓝 0)) ∧
    Tendsto (fun l => operatorNorm (logSeries X - logSeriesPartialSum X l)) atTop (𝓝 0) ∧
    (∀ i j : Fin 2,
      Summable (fun n : Set.Ici (1 : ℕ) => ‖-((((n : ℕ) : ℂ)⁻¹) * ((1 - X) ^ (n : ℕ)) i j)‖) ∧
      HasSum (fun n : Set.Ici (1 : ℕ) => -((((n : ℕ) : ℂ)⁻¹) * ((1 - X) ^ (n : ℕ)) i j))
        (logSeries X i j)) ∧
    (∀ l : ℕ, operatorNorm (logSeries X - logSeriesPartialSum X l) ≤
        ∑' n : Set.Ioi l, t ^ (n : ℕ) / ((n : ℕ) : ℝ) ∧
      ∑' n : Set.Ioi l, t ^ (n : ℕ) / ((n : ℕ) : ℝ) ≤
        t ^ (l + 1) / (((l : ℝ) + 1) * (1 - t))) ∧
    operatorNorm (logSeries X - (X - 1)) ≤ t ^ 2 / (2 * (1 - t)) ∧
    operatorNorm (logSeries X) ≤ -realLog (1 - t)) ∧
  logSeries (1 : ComplexMatrix2) = 0
end ComplexMatrix2
end YangMills.Construction.Matrices
