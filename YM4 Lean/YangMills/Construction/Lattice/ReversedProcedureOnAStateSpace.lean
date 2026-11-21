import YangMills.Construction.Lattice.GaugeConfigSpaces
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.PeriodicLattice.ConfigSpaces
open YangMills.Construction.BorelKernels
universe u
variable {L m K : ℕ} {𝔅 : Finset (GradedBond L m K)} {𝒴 : Type u} [MeasurableSpace 𝒴]
def haarLaw (S : Finset (FourTorus L m)) (_ξ : ConfigSpace 𝔅 𝒴) :
    Measure (FaddeevPopov.SiteGaugeGroup S) :=
  gaugeHaar S
end YangMills.Construction.PeriodicLattice.ConfigSpaces
