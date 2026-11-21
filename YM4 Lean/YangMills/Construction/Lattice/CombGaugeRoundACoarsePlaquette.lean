import YangMills.Construction.Lattice.BondsAndLinearAveragesRoundACoarsePlaquette
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def CoarsePlaquetteCombGauge : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K n : ℕ, 0 < m → n < K →
    ∀ (s : AveragingScheme) (p : PlaquetteAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
    IsGaugeFieldWithin (fourCornerBlockSites p) W →
    maxPlaquetteDeviation (fourCornerBlockSites p) W ≤ stepCurvatureBound L →
    ∃ a : LieBondFieldWithin (fourCornerBlockSites p), IsCompactValued a ∧
      supOperatorNorm a ≤ 3 * Real.pi * L * maxPlaquetteDeviation (fourCornerBlockSites p) W ∧
      (∀ c ∈ ({firstEdge p, secondEdge p, thirdEdge p, fourthEdge p} :
          Set (BondAtLevel L m K (n + 1))),
        supOperatorNorm (LieBondField.restrictToDoubleBlock c a) ≤
          3 * Real.pi * L * maxPlaquetteDeviation (fourCornerBlockSites p) W) ∧
      (∀ q : PlaquetteAtLevel L m K n, q.LiesIn (fourCornerBlockSites p) →
        Matrices.ComplexMatrix2.operatorNorm
          (plaquetteHolonomy (expTwist (LieBondField.matrixValues a) trivialGaugeField) q - 1) ≤
          maxPlaquetteDeviation (fourCornerBlockSites p) W) ∧
      Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy (schemeBlockAverage s W) p - 1) =
        Matrices.ComplexMatrix2.operatorNorm (plaquetteAverageHolonomy s a p - 1)
end YangMills.Construction.PeriodicLattice
end
