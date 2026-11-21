import YangMills.Construction.Lattice.BondsAndLinearAveragesRoundACoarsePlaquette
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def RealBondSumAroundPlaquetteBound : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n ≤ K →
    ∀ (Z : Set (SiteAtLevel L m K n)) (a : LieBondFieldWithin Z), IsCompactValued a →
      supOperatorNorm a ≤ 1 / 4 → ∀ q : PlaquetteAtLevel L m K n, q.LiesIn Z →
        Matrices.ComplexMatrix2.operatorNorm
            (bondFormSumAlong (LieBondField.matrixValues a) q.boundaryBonds) ≤
          Matrices.ComplexMatrix2.operatorNorm
              (plaquetteHolonomy (expTwist (LieBondField.matrixValues a) trivialGaugeField) q
                - 1) + 35 * supOperatorNorm a ^ 2
end YangMills.Construction.PeriodicLattice
