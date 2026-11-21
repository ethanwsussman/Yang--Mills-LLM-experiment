import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BlocksAndCorridors
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K i : ℕ}
structure PivotProperties (c : BondAtLevel L m K (i + 1)) : Prop where
  existsUnique_onAxialPath : ∃! b : BondAtLevel L m K i,
    b ∈ axialPath (c.source.toSublattice (levelDepth K i)) (c.target.toSublattice (levelDepth K i)) ∧
      b ∈ (bondCorridor c : Set (BondAtLevel L m K i))
  isPivot : IsPivot c (pivot c : BondAtLevel L m K i)
  pivot_opposite : (pivot c.opposite : BondAtLevel L m K i) =
    (pivot c : BondAtLevel L m K i).opposite
  axis_eq : (pivot c : BondAtLevel L m K i).axis = c.axis
  isPositivelyOriented_iff : (pivot c : BondAtLevel L m K i).IsPositivelyOriented ↔
    c.IsPositivelyOriented
def PivotOfEveryBond : Prop :=
  ∀ (s : Conventions.StandingParameters) (i : ℕ), i < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (i + 1), PivotProperties c
end PeriodicLattice
end YangMills.Construction
