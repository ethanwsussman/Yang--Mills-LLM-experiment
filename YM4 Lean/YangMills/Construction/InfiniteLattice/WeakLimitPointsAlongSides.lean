import YangMills.Construction.Lattice.BondsOfTheTorusLatticeAndThePeriodicExtension
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace YangMills.Construction
namespace InfiniteLattice
theorem integral_liftedWilsonMeasure (L m K : ℕ) (β : ℝ)
    {A : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ} (hA : IsBoundedObservable A) :
    ∫ U, A U ∂liftedWilsonMeasure L m K β =
      ∫ W, A (liftField L m (K : ℤ) W) ∂PeriodicLattice.wilsonGibbsMeasure L m K β :=
  integral_map (measurable_liftField L m (K : ℤ)).aemeasurable
    hA.1.aestronglyMeasurable
def IsWeakLimitAlongSides (L K : ℕ) (β : ℝ)
    (ν : Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) : Prop :=
  IsProbabilityMeasure ν ∧ ∃ n : ℕ → ℕ, (∀ i, 0 < n i) ∧
    Tendsto (fun i => PeriodicLattice.torusSide L (n i)) atTop atTop ∧
    ∀ F : GaugeField (PeriodicLattice.meshSize L (K : ℤ)) → ℂ, Continuous F →
      Tendsto (fun i => ∫ U, F U ∂liftedWilsonMeasure L (n i) K β) atTop
        (𝓝 (∫ U, F U ∂ν))
def weakLimitsAlongSides (L K : ℕ) (β : ℝ) :
    Set (Measure (GaugeField (PeriodicLattice.meshSize L (K : ℤ)))) :=
  {ν | IsWeakLimitAlongSides L K β ν}
end InfiniteLattice
end YangMills.Construction
