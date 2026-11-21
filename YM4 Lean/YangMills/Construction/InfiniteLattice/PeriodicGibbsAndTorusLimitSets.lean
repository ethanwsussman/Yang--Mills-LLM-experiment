import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def periodicGibbsSet (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsPeriodicGibbs β ν}
def torusLimitSet (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsProbabilityMeasure ν ∧ ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧
    StrictMono (fun i => PeriodicLattice.torusSide L (n i)) ∧
    ∀ A : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, Continuous A →
      Tendsto (fun i => ∫ U, A U ∂liftedWilsonMeasure L (n i) K β) atTop
        (𝓝 (∫ U, A U ∂ν))}
end YangMills.Construction.InfiniteLattice
