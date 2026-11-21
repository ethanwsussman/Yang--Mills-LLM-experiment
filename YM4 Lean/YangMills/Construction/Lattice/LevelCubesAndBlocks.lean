import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K j : ℕ}
abbrev cubeAtLevel (y : SiteAtLevel L m K j) : Set (FourTorus L m) := cubeAround y
abbrev blockAtLevel (i : ℕ) (y : SiteAtLevel L m K j) : Set (FourTorus L m) := refinedBlock (j - i) y
abbrev blockUnionAtLevel (i : ℕ) (Y : Set (SiteAtLevel L m K j)) : Set (FourTorus L m) :=
  refinedBlockUnion (j - i) Y
def bondBlockPair (i : ℕ) (c : BondAtLevel L m K j) : Set (FourTorus L m) :=
  blockAtLevel i c.source ∪ blockAtLevel i c.target
end PeriodicLattice
end YangMills.Construction
