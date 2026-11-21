import YangMills.Construction.Constants.SevenNumbersOfTheOneStepTower
import YangMills.Construction.Lattice.CommonNumbersOfTheTwoFamilies
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def sharedCeiling (L : ℕ) : ℝ :=
  min (SharedConstants.gaugeThreshold L) (OneStepTower.plaquetteSmallness L)
end YangMills.Construction.PeriodicLattice
end
