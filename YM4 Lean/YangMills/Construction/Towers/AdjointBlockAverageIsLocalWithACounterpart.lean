import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels
def AdjointCubeAverageIsLocalPeriodic : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ U ∈ Tower.smallIterateFields L n k, ∀ (j : ℕ) (h : j + 1 ≤ k),
      Periodisation.IsLocalWithPeriodicCounterpart L n
        (Periodisation.CellClass.vertexClass k j (Nat.le_of_succ_le h))
        (Periodisation.CellClass.vertexClass k (j + 1) h) (Tower.meshAt L k (j + 1) / 2)
        (Tower.FullSpace.adjointCubeAverage
          (liftGaugeField L n k j (PeriodicLattice.complexBlockFieldAtLevel j U)))
        (Tower.adjointCubeAverage (PeriodicLattice.complexBlockFieldAtLevel j U))
end YangMills.Construction.LocalKernels
end
