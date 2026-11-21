import YangMills.Construction.Lattice.OneStepPlaquetteGrowth
import Mathlib
open YangMills.Construction.Matrices
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CentredSchemeLinearAverageEq : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K n : ℕ, 0 < m → n < K → ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ (a : LieBondField (doubleBlockSymmetricSet c)) (A : BondAtLevel L m K n → ComplexMatrix2),
        IsBondForm complexLieAlgebra A →
        (∀ b : PositiveBondsOf (doubleBlockSymmetricSet c), A b.1 = (a b : ComplexMatrix2)) →
          linearSchemeBlockAverage .centred (matrixValues a) c = scaledLinearBlockAverage A c
end YangMills.Construction.PeriodicLattice
