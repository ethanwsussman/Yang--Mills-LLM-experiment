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
def MeanKernelsAreLocalNearCells : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ ρ C r : ℝ, 0 < ρ ∧ 0 ≤ C ∧ 0 ≤ r ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      IsLocalNearCells colouredEdgeCell edgeCell
        (fun v => unitNormScale L k • Matrix.of (rescaledOperators L n k (remainderGaugeField v)).Q)
        ρ C r ∧
      IsLocalNearCells colouredEdgeCell edgeCell
        (fun v => unitNormScale L k • Matrix.of (meanKernelQ L n k (remainderGaugeField v)))
        ρ C r ∧
      IsLocalNearCells colouredVertexCell vertexCell
        (fun v => unitNormScale L k • Matrix.of (rescaledOperators L n k (remainderGaugeField v)).R)
        ρ C r ∧
      IsLocalNearCells colouredVertexCell vertexCell
        (fun v => unitNormScale L k • Matrix.of (meanKernelR L n k (remainderGaugeField v)))
        ρ C r
end YangMills.Construction.RunningCouplingSlope
end
