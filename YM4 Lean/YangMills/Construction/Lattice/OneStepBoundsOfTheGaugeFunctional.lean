import YangMills.Construction.Lattice.AveragingOnPart
import YangMills.Construction.Lattice.OneStepOfTheGaugeFunctional
import YangMills.Construction.Lattice.SiteLogarithm
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def blockGaugeDeviation (r : SiteAtLevel L m K n → Matrices.ComplexMatrix2)
    (y : SiteAtLevel L m K (n + 1)) : ℝ :=
  ⨆ x : ↥(sitesInBlock (levelDepth K n) y), Matrices.ComplexMatrix2.operatorNorm (r x - 1)
def blockGaugeMaxAngle (V : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (r : SiteAtLevel L m K n → Matrices.ComplexMatrix2) (y : SiteAtLevel L m K (n + 1)) : ℝ :=
  ⨆ b : ↥(bondsWithin (sitesInBlock (levelDepth K n) y)).bonds,
    Matrices.ComplexMatrix2.rotationAngle (gaugeBondTwist V r b)
def blockFieldNorm {c : BondAtLevel L m K (n + 1)}
    (A : LieBondField (doubleBlockSymmetricSet c)) (y : SiteAtLevel L m K (n + 1)) : ℝ :=
  ⨆ b : ↥(bondsWithin (sitesInBlock (levelDepth K n) y)).bonds,
    Matrices.ComplexMatrix2.operatorNorm (A.eval b.1 : Matrices.ComplexMatrix2)
structure GaugeStepEstimates (κ : ℝ) (c : BondAtLevel L m K (n + 1))
    (A : LieBondField (doubleBlockSymmetricSet c)) (V : BondAtLevel L m K n → Matrices.ComplexMatrix2)
    (r : SiteAtLevel L m K n → Matrices.ComplexMatrix2) : Prop where
  well_defined : GaugeStepDefined c A V r
  norm_le : supOperatorNorm (gaugedLieField c A V r) ≤
    supOperatorNorm A + maxGaugeBondAngle c V r
  norm_lt_radius : supOperatorNorm A + maxGaugeBondAngle c V r < bondFieldRadius L
  dist_le : ∀ y ∈ bondEnds c,
    Matrices.ComplexMatrix2.operatorNorm (gaugeStep c A V r y - 1) ≤
      (1 + κ * doubleBlockCurvature V c) * gaugeDeviation c r + κ * maxGaugeBondAngle c V r
  dist_le_block : ∀ y ∈ bondEnds c,
    Matrices.ComplexMatrix2.operatorNorm (gaugeStep c A V r y - 1) ≤
      (1 + κ * maxPlaquetteDeviation (sitesInBlock (levelDepth K n) y) V) *
          blockGaugeDeviation r y +
        κ * blockGaugeMaxAngle V r y
  angle_le : Matrices.ComplexMatrix2.rotationAngle ((gaugeStep c A V r c.source)⁻¹ *
      Matrices.ComplexMatrix2.conjugateBy
        (partialBlockAverage (Averaging.smoothingRadius L) 1 (doubleBlockSymmetricSet c).bonds V c)
        (gaugeStep c A V r c.target)) ≤
    (L : ℝ) * maxGaugeBondAngle c V r +
      κ * (doubleBlockCurvature V c * gaugeDeviation c r +
        maxGaugeBondAngle c V r ^ 2 + supOperatorNorm A * maxGaugeBondAngle c V r)
  log_le : ∀ y ∈ bondEnds c,
    Matrices.ComplexMatrix2.operatorNorm (Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (gaugeStep c A V r y) -
        covariantBlockAverage V (siteLog r) y) ≤
      κ * (gaugeDeviation c r + supOperatorNorm A) *
        (maxGaugeBondAngle c V r + doubleBlockCurvature V c * gaugeDeviation c r)
  log_le_block : ∀ y ∈ bondEnds c,
    Matrices.ComplexMatrix2.operatorNorm (Complex.I⁻¹ • Matrices.ComplexMatrix2.logSeries (gaugeStep c A V r y) -
        covariantBlockAverage V (siteLog r) y) ≤
      κ * (blockGaugeDeviation r y + blockFieldNorm A y) *
        (blockGaugeMaxAngle V r y +
          maxPlaquetteDeviation (sitesInBlock (levelDepth K n) y) V * blockGaugeDeviation r y)
structure GaugeStepConstants (L : ℕ) (g κ s : ℝ) : Prop where
  angle_pos : 0 < g
  one_le_mult : 1 ≤ κ
  estimates : ∀ m K n : ℕ, 0 < m → n < K → ∀ c : BondAtLevel L m K (n + 1), c.IsPositivelyOriented →
    ∀ V : BondAtLevel L m K n → Matrices.ComplexMatrix2, IsGaugeFieldOnDoubleBlock c V →
    doubleBlockCurvature V c ≤ plaquetteSmallness L →
    ∀ A : LieBondField (doubleBlockSymmetricSet c), IsCompactValued A →
    supOperatorNorm A ≤ bondFieldRadius L / 16 →
    ∀ r : SiteAtLevel L m K n → Matrices.ComplexMatrix2, IsGaugeTransformOnDoubleBlock c r →
    maxGaugeBondAngle c V r ≤ g → gaugeDeviation c r ≤ s →
      GaugeStepEstimates κ c A V r
def IsUniversalDeviationBound (s : ℝ) : Prop :=
  0 < s ∧ s ≤ 1 / 64 ∧
    ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∃ g κ : ℝ, GaugeStepConstants L g κ s
def universalDeviationBound : ℝ := Classical.epsilon IsUniversalDeviationBound
def gaugeStepConstantPair (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun p => GaugeStepConstants L p.1 p.2 universalDeviationBound
def gaugeAngleThreshold (L : ℕ) : ℝ := (gaugeStepConstantPair L).1
def gaugeStepMultiplier (L : ℕ) : ℝ := (gaugeStepConstantPair L).2
end YangMills.Construction.PeriodicLattice
