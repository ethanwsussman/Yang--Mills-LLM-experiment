import YangMills.Construction.RunningCouplingSlope.FamiliesThatReadNearCells
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
open Tower.IteratedSmallFieldMeans (HolomorphicInEntries smallFormBall)
open Tower.LeftChartFields (scalarCoords)
def NoiseCovarianceIsLocalNearCells : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      IsLocalNearCells edgeCell edgeCell
        (fun v => Matrix.of (noiseCovariance a L n k (remainderGaugeField v) k)) ρ C r
end YangMills.Construction.RunningCouplingSlope
end
