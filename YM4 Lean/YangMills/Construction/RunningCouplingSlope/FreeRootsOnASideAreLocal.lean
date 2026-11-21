import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import YangMills.Construction.Towers.HessianOfTheWilsonAction
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def PeriodicResolventSqrtsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)]
        [Fintype (Fin 3 × Tower.Face L n k 0)],
      (periodicEdgeResolventSqrt L n k).transpose = periodicEdgeResolventSqrt L n k ∧
      (periodicVertexResolventSqrt L n k).transpose = periodicVertexResolventSqrt L n k ∧
      IsUnit (Matrix.det (periodicEdgeResolventSqrt L n k)) ∧
      IsUnit (Matrix.det (periodicVertexResolventSqrt L n k)) ∧
      IsLocalOnCells colouredEdgeCell colouredEdgeCell (periodicEdgeResolventSqrt L n k) M θ (fun _ => 1) ∧
      IsLocalOnCells colouredVertexCell colouredVertexCell (periodicVertexResolventSqrt L n k) M θ (fun _ => 1) ∧
      IsLocalOnCells colouredEdgeCell colouredFaceCell
        (Matrix.of (Tower.scaledEdgeCoboundaryKernel L n k 0) * periodicEdgeResolventSqrt L n k) M θ
        (fun _ => 1) ∧
      IsLocalOnCells colouredEdgeCell colouredVertexCell
        ((Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).D).transpose *
          periodicEdgeResolventSqrt L n k) M θ (fun _ => 1) ∧
      IsLocalOnCells colouredVertexCell colouredEdgeCell
        (Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).D *
          periodicVertexResolventSqrt L n k) M θ (fun _ => 1)
end YangMills.Construction.RunningCouplingSlope
end
