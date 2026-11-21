import YangMills.Construction.Lattice.BondsAndLinearAveragesRoundACoarsePlaquette
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CoarsePlaquetteLinearAverageBound.Statement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme)
    (p : PlaquetteAtLevel L m K (n + 1)) (a : LieBondFieldWithin (fourCornerBlockSites p)) (D : ℝ),
    (∀ q : PlaquetteAtLevel L m K n, q.LiesIn (fourCornerBlockSites p) →
      Matrices.ComplexMatrix2.operatorNorm
        (bondFormSumAlong (LieBondField.matrixValues a) q.boundaryBonds) ≤ D) →
    Matrices.ComplexMatrix2.operatorNorm (plaquetteLinearAverage s a p) ≤ (L : ℝ) ^ 2 * D
end YangMills.Construction.PeriodicLattice
