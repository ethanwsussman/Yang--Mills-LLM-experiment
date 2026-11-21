import YangMills.Construction.RunningCouplingSlope.MixedSaddlesOfTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def GhostDeterminantAtQuietPoint : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
      [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
      [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
      [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      ∃ c : ℝ, 0 < c ∧ EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
        |LinearMap.det (ghostBlockOperator (quietPoint U))| = c * ‖Matrix.det (ghostMatrix U)‖
end YangMills.Construction.RunningCouplingSlope
end
