import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels
open Periodisation Tower
def ContourLogDriftIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ U ∈ smallIterateFields L n k, ∀ (j : ℕ) (h : j + 1 ≤ k),
      ∀ V ∈ smallComplexFields L n k j,
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j (Nat.le_of_succ_le h))
        (CellClass.vertexClass k (j + 1) h) (3 * meshAt L k (j + 1) / 2)
        (FullSpace.contourLogDrift (liftGaugeField L n k j V))
        (contourLogDrift V)
end YangMills.Construction.LocalKernels
end
