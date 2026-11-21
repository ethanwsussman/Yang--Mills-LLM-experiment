import YangMills.Construction.Lattice.BondsAndLinearAveragesRoundACoarsePlaquette
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def BlockAverageLogSecondOrderBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
      ∀ a : LieBondField (doubleBlockSymmetricSet c),
        supOperatorNorm a ≤ stepRadius L / 4 →
          Matrices.ComplexMatrix2.matExp (Complex.I • blockAverageLog s c a) =
              schemeBlockAverage s (expBondField c a) c ∧
            Matrices.ComplexMatrix2.operatorNorm (blockAverageLog s c a) ≤
              supOperatorNorm a / stepRadius L ∧
            Matrices.ComplexMatrix2.operatorNorm
                (blockAverageLog s c a - linearSchemeAverage s (LieBondField.matrixValues a) c) ≤
              2 * supOperatorNorm a ^ 2 / stepRadius L ^ 2
end YangMills.Construction.PeriodicLattice
