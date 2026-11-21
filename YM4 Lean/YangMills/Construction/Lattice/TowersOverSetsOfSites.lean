import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
open Set
noncomputable section
namespace YangMills.Construction
open TorusMetric
namespace PeriodicLattice
variable {L m K j : ℕ}
def blockSitesAtLevel (n : ℕ) (y : SiteAtLevel L m K j) : Set (SiteAtLevel L m K n) :=
  {x | (x : FourTorus L m) ∈ blockAtLevel n y}
end PeriodicLattice
end YangMills.Construction
