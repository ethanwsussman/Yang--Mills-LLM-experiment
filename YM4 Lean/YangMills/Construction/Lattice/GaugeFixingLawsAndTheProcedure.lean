import YangMills.Construction.Lattice.IntegralsOfAnAverageAndOfAProcedure
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open YangMills.Construction.BorelKernels
universe u
variable {L m K : ℕ} {E : Finset (GradedBond L m K)} {Y : Type u} [MeasurableSpace Y]
  {S : Finset (FourTorus L m)}
def fixingImage (k : ConfigSpace E Y → Measure (FaddeevPopov.SiteGaugeGroup S))
    (ν : FiniteComplexMeasure (ConfigSpace E Y)) :
    FiniteComplexMeasure (ConfigSpace E Y) :=
  gaugeAveragedMeasure k ν
end YangMills.Construction.PeriodicLattice.ConfigSpaces
end
