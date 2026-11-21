import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def PositiveOrientationOfBondAndOpposite : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j : ℕ, j < K → ∀ c : BondAtLevel L m K (j + 1),
    2 < sideInLevelUnits L m K (j + 1) ∧
    Xor c.IsPositivelyOriented c.opposite.IsPositivelyOriented ∧
    c.positivelyOriented.IsPositivelyOriented ∧
    (c.positivelyOriented = c ∨ c.positivelyOriented = c.opposite) ∧
    Xor (c = c.positivelyOriented) (c = c.positivelyOriented.opposite) ∧
    c.opposite.positivelyOriented = c.positivelyOriented ∧
    (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K j)) = bondsInDoubleBlock c
end PeriodicLattice
end YangMills.Construction
