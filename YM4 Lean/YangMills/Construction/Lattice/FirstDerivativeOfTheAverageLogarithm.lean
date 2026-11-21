import YangMills.Construction.Lattice.BondsAndLinearAveragesRoundACoarsePlaquette
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def HasDerivBlockAverageLogAtZero : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented → ∀ a : LieBondField (doubleBlockSymmetricSet c),
      HasDerivAt (fun t : ℂ => blockAverageLog s c (t • a))
        (linearSchemeAverage s (LieBondField.matrixValues a) c) 0
end YangMills.Construction.PeriodicLattice
