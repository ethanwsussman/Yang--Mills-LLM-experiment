import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {j : ℤ}
def supNormDistInLevelScale (L m K k : ℕ) (x x' : FourTorus L m) : ℝ :=
  toLevelUnits L K k (TorusMetric.torusSupNorm (x - x'))
end YangMills.Construction.PeriodicLattice
end
