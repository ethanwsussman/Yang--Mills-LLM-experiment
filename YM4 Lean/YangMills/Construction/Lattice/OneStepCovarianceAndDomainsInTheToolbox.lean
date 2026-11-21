import YangMills.Construction.Averaging.SingleStepNotation
import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.OneStepObjectsInTheToolbox
import YangMills.Construction.Matrices.GroupLieProducts
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
def projectTraceless (X : ComplexMatrix2) : ↥ComplexMatrix2.traceless :=
  open Classical in if hX : X ∈ ComplexMatrix2.traceless then ⟨X, hX⟩ else 0
variable {L m K n : ℕ}
def bondEnds {j : ℤ} (e : Bond L m j) : Set (Site L m j) := {e.source, e.target}
def bondExponential (e : BondAtLevel L m K (n + 1)) (u : LieBondField (doubleBlockSymmetricSet e)) :
    BondAtLevel L m K n → ComplexMatrix2 :=
  stepTwistedField e u trivialGaugeField
def stepGaugeLogAt (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (u : LieBondField (doubleBlockSymmetricSet e)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (stepGaugeAt σ e u V y)
def averageLogAt (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (u : LieBondField (doubleBlockSymmetricSet e)) : ComplexMatrix2 :=
  Complex.I⁻¹ • ComplexMatrix2.logSeries (oneStepAverage σ (bondExponential e u) e)
def StepLogFormedAt (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (u : LieBondField (doubleBlockSymmetricSet e)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) (x : SiteAtLevel L m K n) : Prop :=
  StepData e V ∧ IsContourHolonomyDefined σ (stepTwistedField e u V) y x ∧
    IsContourHolonomyDefined σ V y x ∧ ComplexMatrix2.operatorNorm (stepRatio σ e u V y x - 1) < 1
def StepGaugeFormedAt (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (u : LieBondField (doubleBlockSymmetricSet e)) (V : BondAtLevel L m K n → ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : Prop :=
  ∀ x ∈ sitesInBlock (levelDepth K n) y, StepLogFormedAt σ e u V y x
structure StepEstimatesNearIdentity (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (u₀ u : LieBondField (doubleBlockSymmetricSet e)) : Prop where
  log_le : ∀ y ∈ bondEnds e, ∀ x ∈ sitesInBlock (levelDepth K n) y,
    StepLogFormedAt σ e u (bondExponential e u₀) y x ∧
      ComplexMatrix2.operatorNorm (stepLogAt σ e u (bondExponential e u₀) y x) ≤ 1
  gauge_le : ∀ y ∈ bondEnds e, StepGaugeFormedAt σ e u (bondExponential e u₀) y ∧
    ComplexMatrix2.operatorNorm (stepGaugeAt σ e u (bondExponential e u₀) y - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (stepGaugeLogAt σ e u (bondExponential e u₀) y) ≤ 1
  variable_le : StepVariableFormed σ e u (bondExponential e u₀) ∧
    ComplexMatrix2.operatorNorm (stepVariableAt σ e u (bondExponential e u₀)) ≤ 1
  average_le : IsOneStepAverageFormed σ (bondExponential e u₀) e ∧
    ComplexMatrix2.operatorNorm (oneStepAverage σ (bondExponential e u₀) e - 1) < 1 ∧
      ComplexMatrix2.operatorNorm (averageLogAt σ e u₀) ≤ 1
  conjugate_le : ∀ x ∈ sitesInBlock (levelDepth K n) e.source, ∀ b ∈ crossingPath e x, ∀ X : ComplexMatrix2,
    ComplexMatrix2.operatorNorm (ComplexMatrix2.conjugateBy
      (contourHolonomy σ (bondExponential e u₀) e.source x *
        pathHolonomy (bondExponential e u₀) (axialPath x b.source)) X) ≤
      2 * ComplexMatrix2.operatorNorm X
def pairLeftField {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun b => projectTraceless (A (.inl b))
def pairRightField {ι : Type} (A : ι ⊕ ι → ComplexMatrix2) : ι → ↥ComplexMatrix2.traceless :=
  fun b => projectTraceless (A (.inr b))
def StepAnalyticNearIdentity (r : ℝ) (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1)) : Prop :=
  ∀ (_ : Fintype (PositiveBondsOf (doubleBlockSymmetricSet e) ⊕ PositiveBondsOf (doubleBlockSymmetricSet e)))
    (β : Module.Basis (Fin 3) ℂ ComplexMatrix2.traceless),
    (∀ y ∈ bondEnds e, ∀ x ∈ sitesInBlock (levelDepth K n) y,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepLogAt σ e (pairRightField A) (bondExponential e (pairLeftField A)) y x) ∧
    (∀ y ∈ bondEnds e,
      GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
        (GroupLieProduct.supBall _ r) fun A =>
          stepGaugeLogAt σ e (pairRightField A) (bondExponential e (pairLeftField A)) y) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) (fun A =>
        stepVariableAt σ e (pairRightField A) (bondExponential e (pairLeftField A))) ∧
    GroupLieProduct.IsHolomorphicOnTraceless β Coordinates.ComplexCoordinates.matrixEquiv
      (GroupLieProduct.supBall _ r) fun A => averageLogAt σ e (pairLeftField A)
section Translation
variable {m' K' n' : ℕ}
structure IsDoubleBlockTranslation (e : BondAtLevel L m K (n + 1)) (e' : BondAtLevel L m' K' (n' + 1))
    (φ : SiteAtLevel L m K n → SiteAtLevel L m' K' n') : Prop where
  bijOn : Set.BijOn φ (sitesIn (bondDoubleBlock e)) (sitesIn (bondDoubleBlock e'))
  map_base : φ (e.source.toSublattice (levelDepth K n)) = e'.source.toSublattice (levelDepth K' n')
  map_add_unitStep : ∀ x ∈ (sitesIn (bondDoubleBlock e) : Set (SiteAtLevel L m K n)), ∀ μ : Fin 4,
    x + unitStep L m (levelDepth K n) μ ∈ (sitesIn (bondDoubleBlock e) : Set (SiteAtLevel L m K n)) →
      φ (x + unitStep L m (levelDepth K n) μ) = φ x + unitStep L m' (levelDepth K' n') μ
def BondFieldsMatchUnder {e : BondAtLevel L m K (n + 1)} {e' : BondAtLevel L m' K' (n' + 1)}
    (φ : SiteAtLevel L m K n → SiteAtLevel L m' K' n') (u : LieBondField (doubleBlockSymmetricSet e))
    (u' : LieBondField (doubleBlockSymmetricSet e')) : Prop :=
  ∀ b ∈ (doubleBlockSymmetricSet e).bonds, ∀ b' ∈ (doubleBlockSymmetricSet e').bonds,
    b'.source = φ b.source → b'.target = φ b.target → u'.eval b' = u.eval b
structure StepValuesMatchUnder (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1))
    (e' : BondAtLevel L m' K' (n' + 1)) (φ : SiteAtLevel L m K n → SiteAtLevel L m' K' n')
    (u₀ u : LieBondField (doubleBlockSymmetricSet e))
    (u₀' u' : LieBondField (doubleBlockSymmetricSet e')) : Prop where
  log_eq : ∀ y y', (y = e.source ∧ y' = e'.source ∨ y = e.target ∧ y' = e'.target) →
    ∀ x ∈ sitesInBlock (levelDepth K n) y,
      stepLogAt σ e' u' (bondExponential e' u₀') y' (φ x) = stepLogAt σ e u (bondExponential e u₀) y x
  gaugeLog_eq : ∀ y y', (y = e.source ∧ y' = e'.source ∨ y = e.target ∧ y' = e'.target) →
    stepGaugeLogAt σ e' u' (bondExponential e' u₀') y' = stepGaugeLogAt σ e u (bondExponential e u₀) y
  variable_eq : stepVariableAt σ e' u' (bondExponential e' u₀') = stepVariableAt σ e u (bondExponential e u₀)
  averageLog_eq : averageLogAt σ e' u₀' = averageLogAt σ e u₀
end Translation
structure IsAdmissibleStepRadius (L : ℕ) (r : ℝ) : Prop where
  pos : 0 < r
  le_inv_sixteen : r ≤ 1 / 16
  estimates : ∀ m K n : ℕ, 0 < m → n < K → ∀ (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1)),
    e.IsPositivelyOriented → ∀ u₀ u : LieBondField (doubleBlockSymmetricSet e),
      supOperatorNorm u₀ < r → supOperatorNorm u < r → StepEstimatesNearIdentity σ e u₀ u
  analytic : ∀ m K n : ℕ, 0 < m → n < K → ∀ (σ : AveragingScheme) (e : BondAtLevel L m K (n + 1)),
    e.IsPositivelyOriented → StepAnalyticNearIdentity r σ e
  translation_invariant : ∀ m K n m' K' n' : ℕ, 0 < m → n < K → 0 < m' → n' < K' →
    ∀ (σ : AveragingScheme) (μ : Fin 4)
    (e : BondAtLevel L m K (n + 1)) (e' : BondAtLevel L m' K' (n' + 1))
    (φ : SiteAtLevel L m K n → SiteAtLevel L m' K' n'),
    e.target - e.source = unitStep L m (levelDepth K (n + 1)) μ →
    e'.target - e'.source = unitStep L m' (levelDepth K' (n' + 1)) μ → IsDoubleBlockTranslation e e' φ →
    ∀ (u₀ u : LieBondField (doubleBlockSymmetricSet e))
      (u₀' u' : LieBondField (doubleBlockSymmetricSet e')),
      supOperatorNorm u₀ < r → supOperatorNorm u < r →
      BondFieldsMatchUnder φ u₀ u₀' → BondFieldsMatchUnder φ u u' →
      StepValuesMatchUnder σ e e' φ u₀ u u₀' u'
def admissibleStepRadius (L : ℕ) : ℝ := Classical.epsilon (IsAdmissibleStepRadius L)
def bondFieldRadius (L : ℕ) : ℝ :=
  min (admissibleStepRadius L)
    (min (Averaging.smoothingRadius L / 8) ((Averaging.SingleStepNotation.kappaTwo L)⁻¹ / 8))
def plaquetteSmallness (L : ℕ) : ℝ :=
  min (Averaging.smoothingRadius L / 2)
    (min ((Averaging.SingleStepNotation.kappaTwo L)⁻¹ / 2)
      (admissibleStepRadius L / (6 * Real.pi * (L : ℝ))))
def stepBoundConstant (L : ℕ) : ℝ := 1 / admissibleStepRadius L
end YangMills.Construction.PeriodicLattice
