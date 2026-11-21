import YangMills.Construction.RunningCouplingSlope.DifferenceOfTheTwoFunctionals
import Mathlib
set_option autoImplicit false
open scoped ComplexOrder
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower PeriodicOperators Conventions
def FlatNoiseCovariancePositive : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 1 ≤ k → 0 < n →
    meanKernelQ L n k (trivialField L n k 0) =
      (rescaledOperators L n k (trivialField L n k 0)).Q ∧
    (Matrix.of (noiseCovariance a L n k (trivialField L n k 0) k)).PosSemidef ∧
    ∀ [Fintype (Fin 3 × PositiveEdge L n k 0)] [Fintype (Fin 3 × PositiveEdge L n k k)]
      [Fintype (Fin 3 × Vertex L n k 0)] [Fintype (Fin 3 × Vertex L n k k)]
      [DecidableEq (Fin 3 × PositiveEdge L n k 0)] [DecidableEq (Fin 3 × PositiveEdge L n k k)]
      [DecidableEq (Fin 3 × Vertex L n k 0)] [DecidableEq (Fin 3 × Vertex L n k k)],
      IsUnit (Matrix.det (Matrix.of (rescaledOperators L n k (trivialField L n k 0)).Xi)) →
        (topCovariance (trivialField L n k 0)).PosSemidef ∧
        (1 - topCovariance (trivialField L n k 0)).PosSemidef
end YangMills.Construction.RunningCouplingSlope
end
