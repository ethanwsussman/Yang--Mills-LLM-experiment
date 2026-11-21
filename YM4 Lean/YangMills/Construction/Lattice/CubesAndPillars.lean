import YangMills.Construction.Lattice.LevelCubesAndBlocks
import Mathlib
set_option autoImplicit false
open YangMills.Construction.PeriodicLattice
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.Pillars
variable {L m K : ℕ}
def coarserSite {i : ℕ} (n : ℕ) (z : SiteAtLevel L m K i) : SiteAtLevel L m K n :=
  Classical.epsilon fun y : SiteAtLevel L m K n => (z : FourTorus L m) ∈ blockAtLevel i y
end YangMills.Construction.Pillars
