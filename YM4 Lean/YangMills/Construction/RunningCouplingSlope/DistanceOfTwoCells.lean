import YangMills.Construction.RunningCouplingSlope.CellsOfATower
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open Tower
def CellDistLowerBound : Prop :=
  ∀ (L n k : ℕ), 0 < L → ∀ w : Fin 4 → ℤ, (∀ μ, |w μ| ≤ (L : ℤ) ^ n) →
    1 / 2 * ∑ μ, |(w μ : ℝ)| ≤ cellDist (cellOfCoords L n k 0) (cellOfCoords L n k w)
end YangMills.Construction.RunningCouplingSlope
end
