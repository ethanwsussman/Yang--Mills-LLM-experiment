import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m : ℕ}
def IsSiteBox (j : ℤ) (P : Set (Site L m j)) : Prop :=
  ∃ (i : ℤ) (X : Set (FourTorus L m)), -(m : ℤ) ≤ i ∧ i ≤ j ∧ IsPartitionBox i X ∧
    (∃ c : TorusBox.BoxChart (torusSide L m) X, ∀ μ, c.upper μ - c.lower μ < torusSide L m / 2) ∧
    P = sitesIn X
end PeriodicLattice
end YangMills.Construction
