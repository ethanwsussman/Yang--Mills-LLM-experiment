import YangMills.Construction.Averaging.SingleStepConstants
import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.AveragesOfExtensions
import YangMills.Construction.Lattice.OneStepObjects
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
open Matrices
def tracelessPart (X : ComplexMatrix2) : ↥ComplexMatrix2.traceless :=
  open Classical in if h : X ∈ ComplexMatrix2.traceless then ⟨X, h⟩ else 0
variable {L m K n : ℕ}
def expOfBondField (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) : BondAtLevel L m K n → ComplexMatrix2 :=
  twistedConfig c a trivialGaugeField
def stepGaugeLogarithm (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (U : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (stepGauge s c a U y)
def schemeAverageLog (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (schemeBlockAverage s (expOfBondField c a) c)
def IsContourRatioLogDefined (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (U : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Prop :=
  IsContourHolonomyDefined s (twistedConfig c a U) y x ∧
    IsContourHolonomyDefined s U y x ∧
      ComplexMatrix2.operatorNorm (stepRatio s c a U y x - 1) < 1
def IsStepGaugeDefined (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (U : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : Prop :=
  ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourRatioLogDefined s c a U y x
structure StepQuantitiesBounded (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (U : BondAtLevel L m K n → ComplexMatrix2) :
    Prop where
  log_bound : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, IsContourRatioLogDefined s c a U y x ∧
      ComplexMatrix2.operatorNorm (stepLog s c a U y x) ≤ 1
  gauge_bound : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    IsStepGaugeDefined s c a U y ∧ ComplexMatrix2.operatorNorm (stepGauge s c a U y - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (stepGaugeLogarithm s c a U y) ≤ 1
  variable_bound : StepVariableDefined s c a U ∧
    ComplexMatrix2.operatorNorm (stepVariable s c a U) ≤ 1
structure PolydiscBounds (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a₀ a : LieBondField (doubleBlockSymmetricSet c)) : Prop where
  quantities : StepQuantitiesBounded s c a (expOfBondField c a₀)
  average_bound : IsSchemeAverageDefined s (expOfBondField c a₀) c ∧
    ComplexMatrix2.operatorNorm (schemeBlockAverage s (expOfBondField c a₀) c - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (schemeAverageLog s c a₀) ≤ 1
  conj_bound : ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ v ∈ crossingPath c x,
    ∀ X : ComplexMatrix2,
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy
      (contourHolonomy s (expOfBondField c a₀) c.source x *
        pathHolonomy (expOfBondField c a₀) (axialPath x v.source)) X) ≤
      2 * ComplexMatrix2.operatorNorm X
def firstComponent {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun v => tracelessPart (A (.inl v))
def secondComponent {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun v => tracelessPart (A (.inr v))
def IsHolomorphicOnPolydisc (r : ℝ) (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) :
    Prop :=
  ∀ (_ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕
      PositiveBondsOf (doubleBlockSymmetricSet c)))
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepLog s c (secondComponent A) (expOfBondField c (firstComponent A)) y x) ∧
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepGaugeLogarithm s c (secondComponent A) (expOfBondField c (firstComponent A)) y) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) (fun A =>
        stepVariable s c (secondComponent A) (expOfBondField c (firstComponent A))) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) fun A => schemeAverageLog s c (firstComponent A)
structure IsAdmissiblePolydiscRadius (L : ℕ) (r : ℝ) : Prop where
  radius_pos : 0 < r
  radius_le : r ≤ 1 / 16
  bounds_on : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented →
    ∀ a₀ a : LieBondField (doubleBlockSymmetricSet c),
      supOperatorNorm a₀ < r → supOperatorNorm a < r → PolydiscBounds s c a₀ a
  holomorphic_on : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)), c.IsPositivelyOriented → IsHolomorphicOnPolydisc r s c
section Chart
variable {m' K' n' : ℕ}
structure IsDoubleBlockChart (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') : Prop where
  bijOn : Set.BijOn f (sitesIn (bondDoubleBlock c)) (sitesIn (bondDoubleBlock c'))
  map_source : f (c.source.toSublattice (levelDepth K n)) =
    c'.source.toSublattice (levelDepth K' n')
  map_unitStep : ∀ x ∈ (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)), ∀ μ : Fin 4,
    x + unitStep L m (levelDepth K n) μ ∈ (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) →
      f (x + unitStep L m (levelDepth K n) μ) = f x + unitStep L m' (levelDepth K' n') μ
def FieldsAgreeInChart {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n')
    (a : LieBondField (doubleBlockSymmetricSet c))
    (a' : LieBondField (doubleBlockSymmetricSet c')) : Prop :=
  ∀ v ∈ (doubleBlockSymmetricSet c).bonds, ∀ v' ∈ (doubleBlockSymmetricSet c').bonds,
    v'.source = f v.source → v'.target = f v.target → a'.eval v' = a.eval v
structure StepValuesAgreeInChart (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (c' : BondAtLevel L m' K' (n' + 1)) (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n')
    (a₀ a : LieBondField (doubleBlockSymmetricSet c))
    (a₀' a' : LieBondField (doubleBlockSymmetricSet c')) : Prop where
  log_eq : ∀ y y', (y = c.source ∧ y' = c'.source ∨ y = c.target ∧ y' = c'.target) →
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      stepLog s c' a' (expOfBondField c' a₀') y' (f x) =
        stepLog s c a (expOfBondField c a₀) y x
  gaugeLog_eq : ∀ y y', (y = c.source ∧ y' = c'.source ∨ y = c.target ∧ y' = c'.target) →
    stepGaugeLogarithm s c' a' (expOfBondField c' a₀') y' =
      stepGaugeLogarithm s c a (expOfBondField c a₀) y
  variable_eq : stepVariable s c' a' (expOfBondField c' a₀') =
    stepVariable s c a (expOfBondField c a₀)
  averageLog_eq : schemeAverageLog s c' a₀' = schemeAverageLog s c a₀
end Chart
def bondRadius (L : ℕ) (r : ℝ) : ℝ :=
  min r (min (Averaging.smoothingRadius L / 8)
    ((Averaging.SingleStep.loopVariableConstant L)⁻¹ / 8))
def curvatureBound (L : ℕ) (r : ℝ) : ℝ :=
  min (Averaging.smoothingRadius L / 2)
    (min ((Averaging.SingleStep.loopVariableConstant L)⁻¹ / 2) (r / (6 * Real.pi * (L : ℝ))))
def StepQuantitiesHolomorphic (ρ : ℝ) (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  ∀ (_ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K n) y,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ ρ) fun A =>
          stepLog s c (fun v => tracelessPart (A v)) U y x) ∧
    (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ ρ) fun A =>
          stepGaugeLogarithm s c (fun v => tracelessPart (A v)) U y) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ ρ) fun A =>
        stepVariable s c (fun v => tracelessPart (A v)) U
structure StepQuantitiesLinearBound (κ : ℝ) (s : AveragingScheme)
    (c : BondAtLevel L m K (n + 1)) (U : BondAtLevel L m K n → ComplexMatrix2)
    (a : LieBondField (doubleBlockSymmetricSet c)) : Prop where
  log_le : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      ComplexMatrix2.operatorNorm (stepLog s c a U y x) ≤ κ * supOperatorNorm a
  gaugeLog_le : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ComplexMatrix2.operatorNorm (stepGaugeLogarithm s c a U y) ≤ κ * supOperatorNorm a
  variable_le : ComplexMatrix2.operatorNorm (stepVariable s c a U) ≤ κ * supOperatorNorm a
structure StepQuantitiesReal (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (U : BondAtLevel L m K n → ComplexMatrix2) (a : LieBondField (doubleBlockSymmetricSet c)) :
    Prop where
  log_mem : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    ∀ x ∈ sitesInBlock (levelDepth K n) y, stepLog s c a U y x ∈ compactLieAlgebra
  gaugeLog_mem : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    stepGaugeLogarithm s c a U y ∈ compactLieAlgebra
  variable_mem : stepVariable s c a U ∈ compactLieAlgebra
  gauge_mem : ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (n + 1))),
    stepGauge s c a U y ∈ compactGaugeGroup
  curvature_lt : doubleBlockCurvature (twistedConfig c a U) c < Averaging.smoothingRadius L
  average_eq : schemeBlockAverage .centred (twistedConfig c a U) c =
    iteratedAverageOfExtension (Averaging.smoothingRadius L) n 1 (twistedConfig c a U) c
end PeriodicLattice
end YangMills.Construction
