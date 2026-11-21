import YangMills.Construction.RunningCouplingSlope.MatricesOfTheWholeChain
import Mathlib
set_option autoImplicit false
open Filter
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower Conventions
def SaddlePointMatrixInverseBounded : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n in atTop,
      ∀ [Fintype (LevelFormIndex L n k)] [DecidableEq (LevelFormIndex L n k)]
        [Fintype (Fin 3 × PositiveEdge L n k k)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
        [Fintype (GhostCoordIndex L n k)] [DecidableEq (GhostCoordIndex L n k)]
        [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
        (P : PauliCoordinates L n k),
        IsUnit (Matrix.det (saddlePointMatrix P a 0)) ∧ ‖(saddlePointMatrix P a 0)⁻¹‖ ≤ K
end YangMills.Construction.RunningCouplingSlope
end
