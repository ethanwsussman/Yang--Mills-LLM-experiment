import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.ContourDriftLocality
open Periodisation
def ContourLogDriftIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ U ∈ Tower.smallIterateFields L n k, ∀ (j : ℕ) (h : j + 1 ≤ k),
      IsLocalWithPeriodicCounterpart L n (CellClass.edgeClass k j (Nat.le_of_succ_le h))
        (CellClass.vertexClass k (j + 1) h) (3 * Tower.meshAt L k (j + 1) / 2)
        (Tower.FullSpace.contourLogDrift
          (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)))
        (Tower.contourLogDrift (PeriodicLattice.complexBlockFieldAtLevel j U))
end YangMills.Construction.LocalKernels.ContourDriftLocality
end
