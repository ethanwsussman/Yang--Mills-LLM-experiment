import YangMills.Construction.RunningCouplingSlope.LocalFamiliesOfCells
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators
open Tower.CriticalBranchResponse
def FreeInversesLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
        [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)]
        [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
      IsUnit (Matrix.det (xiConjugated L n k 0 0 0)) ∧
      IsLocalOnCells colouredEdgeCell colouredEdgeCell (xiConjugated L n k 0 0 0)⁻¹ M θ
        (fun _ => 1) ∧
      IsUnit (Matrix.det (yConjugated L n k 0 0 0)) ∧
      IsLocalOnCells colouredVertexCell colouredVertexCell (yConjugated L n k 0 0 0)⁻¹ M θ
        (fun _ => 1) ∧
      IsUnit (Matrix.det (topCovariance (Tower.trivialField L n k 0))) ∧
      IsLocalOnCells edgeCell edgeCell (topCovariance (Tower.trivialField L n k 0))⁻¹ M θ
        (fun _ => 1) ∧
      IsUnit (Matrix.det (Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).R *
        yInv (Tower.trivialField L n k 0) *
        Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).Rt)) ∧
      IsLocalOnCells vertexCell vertexCell
        (Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).R *
          yInv (Tower.trivialField L n k 0) *
          Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).Rt)⁻¹ M θ
        (fun _ => 1) ∧
      IsUnit (Matrix.det (Matrix.of (meanKernelR L n k (Tower.trivialField L n k 0)) *
        yInv (Tower.trivialField L n k 0) *
        Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).Rt)) ∧
      IsLocalOnCells vertexCell vertexCell
        (Matrix.of (meanKernelR L n k (Tower.trivialField L n k 0)) *
          yInv (Tower.trivialField L n k 0) *
          Matrix.of (Tower.rescaledOperators L n k (Tower.trivialField L n k 0)).Rt)⁻¹ M θ
        (fun _ => 1)
end YangMills.Construction.RunningCouplingSlope
end
