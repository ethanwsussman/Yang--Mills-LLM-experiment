import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def bareLength (L K : ℕ) (r : ℝ) : ℝ := r / meshSize L K
abbrev levelCube (y : SiteAtLevel L m K n) : Set (FourTorus L m) := cubeAround y
def levelPartition (L m K n : ℕ) : Set (Set (FourTorus L m)) :=
  standardCubePartition L m (levelDepth K n)
def siteSingleton (y : SiteAtLevel L m K n) : Set (FourTorus L m) := {(y : FourTorus L m)}
def regionBoundary (i : ℤ) (X : Set (FourTorus L m)) : Set (FourTorus L m) :=
  X ∩ complementRegion i X
end YangMills.Construction.PeriodicLattice
