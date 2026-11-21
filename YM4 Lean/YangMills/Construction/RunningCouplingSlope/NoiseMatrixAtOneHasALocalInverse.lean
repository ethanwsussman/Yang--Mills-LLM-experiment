import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def NoiseMatrixAtTrivialLocalInverse : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
      IsUnit (Matrix.det (noiseBlockMatrix a (Tower.trivialField L n k 0))) ∧
      IsLocalOnCells doubledEdgeCell doubledEdgeCell (noiseBlockMatrix a (Tower.trivialField L n k 0))⁻¹
        M θ (fun _ => 1)
end YangMills.Construction.RunningCouplingSlope
end
