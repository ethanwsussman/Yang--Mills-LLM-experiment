import YangMills.Construction.Geometry.TorusMetric
import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice.CollaredBox
variable {L m : ℕ} {j : ℤ}
def thickening (P : Set (Site L m j)) : Set (Site L m j) :=
  {x | ∃ y ∈ P, TorusMetric.torusSupNorm ((x : FourTorus L m) - (y : FourTorus L m)) ≤ meshSize L j}
end YangMills.Construction.PeriodicLattice.CollaredBox
