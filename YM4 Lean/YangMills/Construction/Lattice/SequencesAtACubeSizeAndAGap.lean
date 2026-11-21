import YangMills.Construction.Lattice.PeriodicLattices
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction
open PeriodicLattice
namespace RegionChains
variable {L m : ℕ}
def meshAtLevel (L n j : ℕ) : ℝ := (L : ℝ) ^ j * finestMeshInLevelUnits L n
def sitesPerAxis (L m K n : ℕ) : ℝ := 2 * (L : ℝ) ^ ((m : ℤ) + levelDepth K n)
end RegionChains
end YangMills.Construction
