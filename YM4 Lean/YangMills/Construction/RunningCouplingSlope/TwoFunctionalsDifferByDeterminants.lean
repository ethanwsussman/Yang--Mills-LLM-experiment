import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def FunctionalDifferenceIsTopDeterminants : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    ∀ [Fintype (Fin 3 × Tower.PositiveEdge L n k 0)] [Fintype (Fin 3 × Tower.PositiveEdge L n k k)]
      [Fintype (Fin 3 × Tower.Vertex L n k 0)] [Fintype (Fin 3 × Tower.Vertex L n k k)]
      [DecidableEq (Fin 3 × Tower.PositiveEdge L n k 0)] [DecidableEq (Fin 3 × Tower.PositiveEdge L n k k)]
      [DecidableEq (Fin 3 × Tower.Vertex L n k 0)] [DecidableEq (Fin 3 × Tower.Vertex L n k k)],
      ∃ c : ℝ, Tower.EventuallyNearIdentity (Tower.fieldSpace L n k 0) fun U =>
        (Matrix.det (noiseBlockMatrix a U) ≠ 0 ∧
          Matrix.det (topCovariance U) ≠ 0 ∧
          Matrix.det (Matrix.of (meanKernelR L n k U) * yInv U *
            Matrix.of (rescaledOperators L n k U).Rt) ≠ 0 ∧
          Matrix.det (Matrix.of (rescaledOperators L n k U).R * yInv U *
            Matrix.of (rescaledOperators L n k U).Rt) ≠ 0) →
        chainMinusBackground a U = topLogDeterminants a U + c
end YangMills.Construction.RunningCouplingSlope
end
