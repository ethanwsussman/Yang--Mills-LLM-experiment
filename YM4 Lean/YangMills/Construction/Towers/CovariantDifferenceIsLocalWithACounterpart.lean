import YangMills.Construction.Towers.LocalLinearMapsWithAPeriodicCounterpart
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LocalKernels.CovDiffLocality
open Periodisation
def CovDiffIsLocal : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k n : ℕ, 0 < n →
    ∀ (j : ℕ) (h : j ≤ k), ∀ V ∈ Tower.fieldsIn L n k j PeriodicLattice.complexGaugeGroup,
      IsLocalWithPeriodicCounterpart L n (CellClass.vertexClass k j h) (CellClass.edgeClass k j h)
        (Tower.meshAt L k j)
        (Tower.FullSpace.covDiff (liftGaugeField L n k j V))
        (Tower.covDiff V)
end YangMills.Construction.LocalKernels.CovDiffLocality
end
