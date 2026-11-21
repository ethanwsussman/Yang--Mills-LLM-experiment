import YangMills.Construction.Lattice.OneStepPlaquetteGrowthInTheToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def smallPlaquetteThreshold (L : ℕ) : ℝ :=
  min ((1 / 2) * plaquetteGrowthRadius L) ((L : ℝ) ^ 2 / (4 * plaquetteGrowthConstant L))
end YangMills.Construction.PeriodicLattice
