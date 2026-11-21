import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice.VolumeLimitSymmetries
def Statement : Prop :=
  ∀ (L : ℕ), Conventions.IsAdmissibleBlockingFactor L → ∀ (K : ℕ+) (β : ℝ), 0 < β →
    ∀ ν : Measure (GaugeField (PeriodicLattice.meshSize L ((K : ℕ) : ℤ))),
      IsInfiniteVolumeLimit L K β ν →
      ∃ _ : IsProbabilityMeasure ν, IsPeriodicGibbs β ν ∧
        PeriodicGibbsAtSpacing.HasSymmetriesAndReflectionPositivity ν
end YangMills.Construction.InfiniteLattice.VolumeLimitSymmetries
