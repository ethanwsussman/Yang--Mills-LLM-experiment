import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
def BackgroundMeansAreLocal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
      ∀ z : Fin 4 → ℤ,
        IsLocalAlongBackground colouredEdgeCell edgeCell (rescaledQAlong L n k z) z M θ ∧
        IsLocalAlongBackground colouredEdgeCell edgeCell (meanQAlong L n k z) z M θ ∧
        IsLocalAlongBackground colouredVertexCell vertexCell (rescaledRAlong L n k z) z M θ ∧
        IsLocalAlongBackground colouredVertexCell vertexCell (meanRAlong L n k z) z M θ ∧
        IsLocalAlongBackground edgeCell edgeCell (noiseAlong a L n k z) z M θ
end YangMills.Construction.RunningCouplingSlope
end
