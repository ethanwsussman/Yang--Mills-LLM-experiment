import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K n : ℕ}
def doubleBlockRestriction (c : BondAtLevel L m K (n + 1))
    (a : LieBondFunction L m (levelDepth K n)) : LieBondField (doubleBlockSymmetricSet c) :=
  fun v => a ⟨v.1, v.2.2⟩
def stepGaugeAtSite (s : AveragingScheme) (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n)) (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  stepGauge s (Bond.forwardFrom y 0) (doubleBlockRestriction (Bond.forwardFrom y 0) a) W₀ y
def transformedBondRatio (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n))
    (r : SiteAtLevel L m K n → ComplexMatrix2) (v : BondAtLevel L m K n) : ComplexMatrix2 :=
  gaugeTransform r (LieBondFunction.twist a W₀) v * (W₀ v)⁻¹
def transformedBondFunction (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n))
    (r : SiteAtLevel L m K n → ComplexMatrix2) : LieBondFunction L m (levelDepth K n) :=
  fun v => toTraceless (Complex.I⁻¹ • ComplexMatrix2.logSeries (transformedBondRatio W₀ a r v.1))
def IsStepDatum (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n)) : Prop :=
  ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    IsGaugeField compactGaugeGroup (doubleBlockSymmetricSet c).bonds W₀ ∧
      doubleBlockCurvature W₀ c ≤ stepCurvatureBound L ∧
      supOperatorNorm (doubleBlockRestriction c a) < stepBondRadius L ∧
      IsCompactValued (doubleBlockRestriction c a)
def TransformedBondFunctionDefined (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n)) (r : SiteAtLevel L m K n → ComplexMatrix2) : Prop :=
  IsStepDatum W₀ a ∧ IsGaugeMap compactGaugeGroup r ∧
    ∀ v : BondAtLevel L m K n, v.IsPositivelyOriented →
      ComplexMatrix2.operatorNorm (transformedBondRatio W₀ a r v - 1) < 1
def gaugeRecursionStep (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n))
    (r : SiteAtLevel L m K n → ComplexMatrix2) (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  (stepGaugeAtSite .centred W₀ (transformedBondFunction W₀ a r) y)⁻¹ *
    r (y.toSublattice (levelDepth K n)) * stepGaugeAtSite .centred W₀ a y
def GaugeRecursionStepDefined (W₀ : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondFunction L m (levelDepth K n)) (r : SiteAtLevel L m K n → ComplexMatrix2) : Prop :=
  TransformedBondFunctionDefined W₀ a r ∧
    supOperatorNorm (transformedBondFunction W₀ a r) < stepBondRadius L
end YangMills.Construction.PeriodicLattice
