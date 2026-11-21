import YangMills.Construction.Towers.TheFunctionalInTheBackgroundGauge
import YangMills.Construction.Towers.TheScaledPicture
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def BackgroundGaugeSaddleDeterminants : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
      [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
      [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
      [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
      ∃ c c' : ℝ, 0 < c ∧ 0 < c' ∧ Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
        |Tower.hessianSaddleDet U 0 0| =
          c * ‖Matrix.det (Matrix.of (Tower.rescaledOperators L n k U).saddleX)‖ ∧
        |Tower.ghostSaddleDet L n k U| =
          c' * ‖Matrix.det (Matrix.of (Tower.rescaledOperators L n k U).saddleDelta)‖
end YangMills.Construction.RunningCouplingSlope
end
