import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.OneStepPlaquetteGrowthInTheToolbox
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CentredLinearAverageEqScaled : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K n : ℕ, 0 < m → n < K → ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
      ∀ a : LieBondField (doubleBlockSymmetricSet c),
        (∃ A : BondAtLevel L m K n → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A ∧
          ∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
            A b.1 = (a b : Matrices.ComplexMatrix2)) ∧
        ∀ A : BondAtLevel L m K n → Matrices.ComplexMatrix2, IsBondForm complexLieAlgebra A →
          (∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
            A b.1 = (a b : Matrices.ComplexMatrix2)) →
            linearStepAverage .centred (lieFieldMatrices a) c =
              scaledLinearBlockAverage A c
end YangMills.Construction.PeriodicLattice
