import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def DifferenceKernelDecaysOnLargeTori : Prop :=
  ∀ a : ℝ, 0 < a → ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ θ C : ℝ, 0 < θ ∧ 0 ≤ C ∧
    ∀ k : ℕ, 1 ≤ k → ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → 0 < n → ∀ z : Fin 4 → ℤ,
      |differenceKernelFinite a L n k z| ≤
        C * Real.exp (-(θ * cellDist (cellOfCoords L n k 0) (cellOfCoords L n k z)))
end YangMills.Construction.RunningCouplingSlope
end
