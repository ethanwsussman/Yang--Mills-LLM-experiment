import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def FourFamiliesLocal : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ M θ : ℝ, 0 < M ∧ 0 < θ ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n →
      ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      ∀ w : Fin 4 → ℤ,
        IsLocalFamily doubledEdgeCell
            (fun s t => noiseBlockMatrix a (twoSourceBackground L n k w s t)) w M θ ∧
        IsLocalFamily edgeCell
            (fun s t => topCovariance (twoSourceBackground L n k w s t)) w M θ ∧
        IsLocalFamily vertexCell
            (fun s t => Matrix.of (meanKernelR L n k (twoSourceBackground L n k w s t)) *
              yInv (twoSourceBackground L n k w s t) *
              Matrix.of (rescaledOperators L n k (twoSourceBackground L n k w s t)).Rt) w M θ ∧
        IsLocalFamily vertexCell
            (fun s t => Matrix.of (rescaledOperators L n k (twoSourceBackground L n k w s t)).R *
              yInv (twoSourceBackground L n k w s t) *
              Matrix.of (rescaledOperators L n k (twoSourceBackground L n k w s t)).Rt) w M θ
end YangMills.Construction.RunningCouplingSlope
end
