import YangMills.Construction.Averaging.SingleStepConstants
import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOfExtensions
import YangMills.Construction.Lattice.OneStepObjects
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
def toTraceless (X : ComplexMatrix2) : ↥ComplexMatrix2.traceless :=
  open Classical in if hX : X ∈ ComplexMatrix2.traceless then ⟨X, hX⟩ else 0
theorem conjugateBy_specialUnitary_traceless_mem (U : ComplexMatrix2.specialUnitary)
    (B : ↥ComplexMatrix2.traceless) :
    ComplexMatrix2.conjugateBy (U : ComplexMatrix2) (B : ComplexMatrix2) ∈ ComplexMatrix2.traceless := by
  have hdet : IsUnit (U : ComplexMatrix2).det := by
    rw [(Matrix.mem_specialUnitaryGroup_iff.mp U.2).2]
    exact isUnit_one
  have hB : ComplexMatrix2.fullTrace (B : ComplexMatrix2) = 0 := B.2
  change ComplexMatrix2.fullTrace (ComplexMatrix2.conjugateBy (U : ComplexMatrix2) (B : ComplexMatrix2)) = 0
  rw [ComplexMatrix2.conjugateBy, ComplexMatrix2.fullTrace, Matrix.trace_mul_comm, ← mul_assoc,
    Matrix.nonsing_inv_mul _ hdet, one_mul]
  exact hB
variable {L m K n : ℕ}
def gaugeMatrixValues (g : SiteAtLevel L m K n → ComplexMatrix2.specialUnitary) :
    SiteAtLevel L m K n → ComplexMatrix2 :=
  fun x => (g x : ComplexMatrix2)
def conjugateBondField {P : SymmetricBondSet L m K n} (g : SiteAtLevel L m K n → ComplexMatrix2.specialUnitary)
    (a : LieBondField P) : LieBondField P :=
  fun b => ⟨ComplexMatrix2.conjugateBy (g b.1.source : ComplexMatrix2) (a b : ComplexMatrix2),
    conjugateBy_specialUnitary_traceless_mem (g b.1.source) (a b)⟩
def bondEndpoints {j : ℤ} (c : Bond L m j) : Set (Site L m j) := {c.source, c.target}
def expBondField (c : BondAtLevel L m K (n + 1)) (a : LieBondField (doubleBlockSymmetricSet c)) :
    BondAtLevel L m K n → ComplexMatrix2 :=
  twistedConfig c a trivialGaugeField
def stepGaugeLog (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (stepGauge s c a W y)
def blockAverageLog (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (schemeBlockAverage s (expBondField c a) c)
def StepLogDefinedAt (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Prop :=
  IsContourHolonomyDefined s (twistedConfig c a W) y x ∧
    IsContourHolonomyDefined s W y x ∧ ComplexMatrix2.operatorNorm (stepRatio s c a W y x - 1) < 1
def StepGaugeDefinedAt (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : Prop :=
  ∀ x ∈ sitesInBlock (levelDepth K n) y, StepLogDefinedAt s c a W y x
def StraightenedMapDefined (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  ∀ x ∈ sitesInBlock (levelDepth K n) c.source, IsContourHolonomyDefined s W c.source x
structure StepCovariance (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a : LieBondField (doubleBlockSymmetricSet c)) (W : BondAtLevel L m K n → ComplexMatrix2)
    (g : SiteAtLevel L m K n → ComplexMatrix2.specialUnitary) : Prop where
  configuration : ∀ b ∈ (doubleBlockSymmetricSet c).bonds,
    gaugeTransform (gaugeMatrixValues g) (twistedConfig c a W) b =
      twistedConfig c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) b
  logarithm : ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
    StepLogDefinedAt s c a W y x →
      StepLogDefinedAt s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) y x ∧
        stepLog s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) y x =
          ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) y) : ComplexMatrix2)
            (stepLog s c a W y x)
  gauge : ∀ y ∈ bondEndpoints c, StepGaugeDefinedAt s c a W y →
    StepGaugeDefinedAt s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) y ∧
      stepGauge s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) y =
        (g (schemeBaseSite s (levelDepth K n) y) : ComplexMatrix2) * stepGauge s c a W y *
          (g (schemeBaseSite s (levelDepth K n) y) : ComplexMatrix2)⁻¹
  variable_eq : StepVariableDefined s c a W →
    StepVariableDefined s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) ∧
      stepVariable s c (conjugateBondField g a) (gaugeTransform (gaugeMatrixValues g) W) =
        ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) c.source) : ComplexMatrix2)
          (stepVariable s c a W)
  operator : StraightenedMapDefined s c W →
    StraightenedMapDefined s c (gaugeTransform (gaugeMatrixValues g) W) ∧
      straightenedMap s c (gaugeTransform (gaugeMatrixValues g) W) (conjugateBondField g a) =
        ComplexMatrix2.conjugateBy (g (schemeBaseSite s (levelDepth K n) c.source) : ComplexMatrix2)
          (straightenedMap s c W a)
structure StepBoundsNearIdentity (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (a₀ a : LieBondField (doubleBlockSymmetricSet c)) : Prop where
  logarithm : ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
    StepLogDefinedAt s c a (expBondField c a₀) y x ∧
      ComplexMatrix2.operatorNorm (stepLog s c a (expBondField c a₀) y x) ≤ 1
  gauge : ∀ y ∈ bondEndpoints c, StepGaugeDefinedAt s c a (expBondField c a₀) y ∧
    ComplexMatrix2.operatorNorm (stepGauge s c a (expBondField c a₀) y - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (stepGaugeLog s c a (expBondField c a₀) y) ≤ 1
  variable_le : StepVariableDefined s c a (expBondField c a₀) ∧
    ComplexMatrix2.operatorNorm (stepVariable s c a (expBondField c a₀)) ≤ 1
  average : IsSchemeAverageDefined s (expBondField c a₀) c ∧
    ComplexMatrix2.operatorNorm (schemeBlockAverage s (expBondField c a₀) c - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (blockAverageLog s c a₀) ≤ 1
  adjoint : ∀ x ∈ sitesInBlock (levelDepth K n) c.source, ∀ b ∈ crossingPath c x, ∀ X : ComplexMatrix2,
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy
      (contourHolonomy s (expBondField c a₀) c.source x *
        pathHolonomy (expBondField c a₀) (axialPath x b.source)) X) ≤
      2 * ComplexMatrix2.operatorNorm X
def pairFirst {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun b => toTraceless (A (.inl b))
def pairSecond {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun b => toTraceless (A (.inr b))
def StepHolomorphicNearIdentity (r : ℝ) (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ (_ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c) ⊕ PositiveBondsOf (doubleBlockSymmetricSet c)))
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
    (∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepLog s c (pairSecond A) (expBondField c (pairFirst A)) y x) ∧
    (∀ y ∈ bondEndpoints c,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepGaugeLog s c (pairSecond A) (expBondField c (pairFirst A)) y) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) (fun A =>
        stepVariable s c (pairSecond A) (expBondField c (pairFirst A))) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) fun A => blockAverageLog s c (pairFirst A)
section Chart
variable {m' K' n' : ℕ}
structure IsDoubleBlockChartMap (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') : Prop where
  bijOn_sites : Set.BijOn f (sitesIn (bondDoubleBlock c)) (sitesIn (bondDoubleBlock c'))
  map_base : f (c.source.toSublattice (levelDepth K n)) = c'.source.toSublattice (levelDepth K' n')
  map_add_unitStep : ∀ x ∈ (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)), ∀ μ : Fin 4,
    x + unitStep L m (levelDepth K n) μ ∈ (sitesIn (bondDoubleBlock c) : Set (SiteAtLevel L m K n)) →
      f (x + unitStep L m (levelDepth K n) μ) = f x + unitStep L m' (levelDepth K' n') μ
def BondFieldsAgreeInChart {c : BondAtLevel L m K (n + 1)} {c' : BondAtLevel L m' K' (n' + 1)}
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n') (a : LieBondField (doubleBlockSymmetricSet c))
    (a' : LieBondField (doubleBlockSymmetricSet c')) : Prop :=
  ∀ b ∈ (doubleBlockSymmetricSet c).bonds, ∀ b' ∈ (doubleBlockSymmetricSet c').bonds,
    b'.source = f b.source → b'.target = f b.target → a'.eval b' = a.eval b
structure StepQuantitiesAgreeInChart (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (c' : BondAtLevel L m' K' (n' + 1)) (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n')
    (a₀ a : LieBondField (doubleBlockSymmetricSet c))
    (a₀' a' : LieBondField (doubleBlockSymmetricSet c')) : Prop where
  logarithm : ∀ y y', (y = c.source ∧ y' = c'.source ∨ y = c.target ∧ y' = c'.target) →
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      stepLog s c' a' (expBondField c' a₀') y' (f x) = stepLog s c a (expBondField c a₀) y x
  gauge : ∀ y y', (y = c.source ∧ y' = c'.source ∨ y = c.target ∧ y' = c'.target) →
    stepGaugeLog s c' a' (expBondField c' a₀') y' = stepGaugeLog s c a (expBondField c a₀) y
  variable_eq : stepVariable s c' a' (expBondField c' a₀') = stepVariable s c a (expBondField c a₀)
  average : blockAverageLog s c' a₀' = blockAverageLog s c a₀
end Chart
structure IsStepRadius (L : ℕ) (r : ℝ) : Prop where
  pos : 0 < r
  le : r ≤ 1 / 16
  bounds : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
    c.IsPositivelyOriented → ∀ a₀ a : LieBondField (doubleBlockSymmetricSet c),
      supOperatorNorm a₀ < r → supOperatorNorm a < r → StepBoundsNearIdentity s c a₀ a
  holomorphic : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
    c.IsPositivelyOriented → StepHolomorphicNearIdentity r s c
  universal : ∀ m K n m' K' n' : ℕ, 0 < m → n < K → 0 < m' → n' < K' → ∀ (s : AveragingScheme) (μ : Fin 4)
    (c : BondAtLevel L m K (n + 1)) (c' : BondAtLevel L m' K' (n' + 1))
    (f : SiteAtLevel L m K n → SiteAtLevel L m' K' n'),
    c.target - c.source = unitStep L m (levelDepth K (n + 1)) μ →
    c'.target - c'.source = unitStep L m' (levelDepth K' (n' + 1)) μ → IsDoubleBlockChartMap c c' f →
    ∀ (a₀ a : LieBondField (doubleBlockSymmetricSet c))
      (a₀' a' : LieBondField (doubleBlockSymmetricSet c')),
      supOperatorNorm a₀ < r → supOperatorNorm a < r →
      BondFieldsAgreeInChart f a₀ a₀' → BondFieldsAgreeInChart f a a' →
      StepQuantitiesAgreeInChart s c c' f a₀ a a₀' a'
def stepRadius (L : ℕ) : ℝ := Classical.epsilon (IsStepRadius L)
def stepBondRadius (L : ℕ) : ℝ :=
  min (stepRadius L)
    (min (Averaging.smoothingRadius L / 8) ((Averaging.SingleStep.loopVariableConstant L)⁻¹ / 8))
def stepCurvatureBound (L : ℕ) : ℝ :=
  min (Averaging.smoothingRadius L / 2)
    (min ((Averaging.SingleStep.loopVariableConstant L)⁻¹ / 2)
      (stepRadius L / (6 * Real.pi * (L : ℝ))))
def stepBallConstant (L : ℕ) : ℝ := 1 / stepRadius L
structure StepBoundsOnBall (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → ComplexMatrix2) (a : LieBondField (doubleBlockSymmetricSet c)) : Prop where
  logarithm : ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
    StepLogDefinedAt s c a W y x ∧ ComplexMatrix2.operatorNorm (stepLog s c a W y x) ≤ 1 ∧
      ComplexMatrix2.operatorNorm (stepLog s c a W y x) ≤ stepBallConstant L * supOperatorNorm a
  gauge : ∀ y ∈ bondEndpoints c, StepGaugeDefinedAt s c a W y ∧
    ComplexMatrix2.operatorNorm (stepGauge s c a W y - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (stepGaugeLog s c a W y) ≤ 1 ∧
        ComplexMatrix2.operatorNorm (stepGaugeLog s c a W y) ≤ stepBallConstant L * supOperatorNorm a
  variable_le : StepVariableDefined s c a W ∧ ComplexMatrix2.operatorNorm (stepVariable s c a W) ≤ 1 ∧
    ComplexMatrix2.operatorNorm (stepVariable s c a W) ≤ stepBallConstant L * supOperatorNorm a
def StepHolomorphicOnBall (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → ComplexMatrix2) : Prop :=
  ∀ (_ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet c)))
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
    (∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ (stepBondRadius L)) fun A =>
          stepLog s c (fun b => toTraceless (A b)) W y x) ∧
    (∀ y ∈ bondEndpoints c,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ (stepBondRadius L)) fun A =>
          stepGaugeLog s c (fun b => toTraceless (A b)) W y) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ (stepBondRadius L)) fun A =>
        stepVariable s c (fun b => toTraceless (A b)) W
structure StepCompactFacts (s : AveragingScheme) (c : BondAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → ComplexMatrix2) (a : LieBondField (doubleBlockSymmetricSet c)) : Prop where
  logarithm : ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
    stepLog s c a W y x ∈ compactLieAlgebra
  gaugeLogarithm : ∀ y ∈ bondEndpoints c, stepGaugeLog s c a W y ∈ compactLieAlgebra
  variable_mem : stepVariable s c a W ∈ compactLieAlgebra
  gauge : ∀ y ∈ bondEndpoints c, stepGauge s c a W y ∈ compactGaugeGroup
  plaquettes : doubleBlockCurvature (twistedConfig c a W) c < Averaging.smoothingRadius L
  average : schemeBlockAverage .centred (twistedConfig c a W) c =
    iteratedAverageOfExtension (Averaging.smoothingRadius L) n 1 (twistedConfig c a W) c
def stepCovarianceDomainsStatement : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    (∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
      c.IsPositivelyOriented →
      ∀ (W : BondAtLevel L m K n → ComplexMatrix2) (a : LieBondField (doubleBlockSymmetricSet c))
        (g : SiteAtLevel L m K n → ComplexMatrix2.specialUnitary),
        IsGaugeField complexGaugeGroup (doubleBlockSymmetricSet c).bonds W →
          StepCovariance s c a W g) ∧
    IsStepRadius L (stepRadius L) ∧
    ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
      c.IsPositivelyOriented →
      ∀ W : BondAtLevel L m K n → ComplexMatrix2,
        IsGaugeField compactGaugeGroup (doubleBlockSymmetricSet c).bonds W →
        doubleBlockCurvature W c ≤ stepCurvatureBound L →
          (∀ a : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm a < stepBondRadius L →
            StepBoundsOnBall s c W a) ∧
          StepHolomorphicOnBall s c W ∧
          ∀ a : LieBondField (doubleBlockSymmetricSet c), supOperatorNorm a < stepBondRadius L →
            IsCompactValued a → StepCompactFacts s c W a
end YangMills.Construction.PeriodicLattice
