import YangMills.Construction.RunningCouplingSlope.MixedSaddlesOfTheTop
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.Tower
def QuietSaddleDetEqSaddleMatrixDet : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
      [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
      [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
      [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      ∃ c : ℝ, 0 < c ∧ EventuallyNearIdentity (fieldSpace L n k 0) fun U =>
        |levelSaddleDet (gaugedOperator a (quietPoint U) 0 0) (shiftedGaugeMap (quietPoint U))| =
          c * Real.exp (3 * logRadiusSum (quietPoint U)) * ‖Matrix.det (saddleMatrix a U)‖
end YangMills.Construction.RunningCouplingSlope
end
