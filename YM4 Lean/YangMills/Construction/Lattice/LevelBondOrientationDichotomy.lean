import YangMills.Construction.Conventions.StandingParameters
import Mathlib
namespace YangMills.Construction.PeriodicLattice
def LevelBondOrientationDichotomy : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
  ∀ j : ℕ, j ≤ K → ∀ b : BondAtLevel L m K j,
    Xor b.IsPositivelyOriented b.opposite.IsPositivelyOriented
end YangMills.Construction.PeriodicLattice
