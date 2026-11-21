import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ} {j j' : ℤ}
def setSupDistInLevelUnits (K n : ℕ) (A B : Set (FourTorus L m)) : ℝ≥0∞ :=
  ENNReal.ofReal (toLevelUnits L K n 1) * TorusMetric.setSupDist A B
def bondSupDist (K n : ℕ) (b : Bond L m j) (b' : Bond L m j') : ℝ≥0∞ :=
  setSupDistInLevelUnits K n b.edgeSet b'.edgeSet
end PeriodicLattice
end YangMills.Construction
