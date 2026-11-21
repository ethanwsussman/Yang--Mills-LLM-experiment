import YangMills.Construction.Lattice.GaugeFunctionalData
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsInTheToolbox
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def gaugeTransformedRatio (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) (b : BondAtLevel L m K n) :
    Matrices.ComplexMatrix2 :=
  gaugeTransform g (stepTwistedField c a U) b * (U b)⁻¹
def gaugedLieField (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) :
    LieBondField (doubleBlockSymmetricSet c) :=
  fun b => projectTraceless
    (Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (gaugeTransformedRatio c a U g b.1))
structure GaugeStepHypotheses (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  level_lt : n < K
  oriented : c.IsPositivelyOriented
  gaugeField : IsGaugeFieldOnDoubleBlock c U
  transform : IsGaugeTransformOnDoubleBlock c g
  curvature_le : doubleBlockCurvature U c ≤ plaquetteSmallness L
  compact : IsCompactValued a
  norm_lt : supOperatorNorm a < bondFieldRadius L
def GaugedLieFieldDefined (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  GaugeStepHypotheses c a U g ∧
    ∀ b : PositiveBondsOf (doubleBlockSymmetricSet c),
      Matrices.ComplexMatrix2.operatorNorm (gaugeTransformedRatio c a U g b.1 - 1) < 1
def GaugeStepDefined (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : Prop :=
  GaugedLieFieldDefined c a U g ∧ supOperatorNorm (gaugedLieField c a U g) < bondFieldRadius L
def gaugeStep (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c))
    (U : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (g : SiteAtLevel L m K n → Matrices.ComplexMatrix2) (y : SiteAtLevel L m K (n + 1)) :
    Matrices.ComplexMatrix2 :=
  (centredStepGauge c (gaugedLieField c a U g) U y)⁻¹ * g (y.toSublattice (levelDepth K n)) *
    centredStepGauge c a U y
end YangMills.Construction.PeriodicLattice
