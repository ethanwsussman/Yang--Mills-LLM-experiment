import YangMills.Construction.Lattice.OneStepCovarianceAndDomains
import Mathlib
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def plaquetteCornerBlockSites (p : PlaquetteAtLevel L m K (n + 1)) : Set (SiteAtLevel L m K n) :=
  sitesIn (refinedBlockUnion 1 p.vertices)
structure IsCurvatureGrowthPair (L : ℕ) (C ϖ' : ℝ) : Prop where
  one_le_const : 1 ≤ C
  radius_pos : 0 < ϖ'
  radius_le : ϖ' ≤ stepCurvatureBound L
  curvature_growth : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme)
    (p : PlaquetteAtLevel L m K (n + 1)) (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
    IsGaugeFieldWithin (plaquetteCornerBlockSites p) W →
    maxPlaquetteDeviation (plaquetteCornerBlockSites p) W ≤ ϖ' →
      Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy (schemeBlockAverage s W) p - 1) ≤
        (L : ℝ) ^ 2 * maxPlaquetteDeviation (plaquetteCornerBlockSites p) W +
          C * maxPlaquetteDeviation (plaquetteCornerBlockSites p) W ^ 2
def curvatureGrowthPair (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun p => IsCurvatureGrowthPair L p.1 p.2
def curvatureGrowthConst (L : ℕ) : ℝ := (curvatureGrowthPair L).1
def curvatureGrowthRadius (L : ℕ) : ℝ := (curvatureGrowthPair L).2
def linearSchemeBlockAverage {j j' : ℤ} (s : AveragingScheme) (a : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock j' c.source, (contourFormMean s a c.source x +
    bondFormSumAlong a (crossingPath c x) - contourFormMean s a c.target (shiftAcross c x))
def matrixValues {c : BondAtLevel L m K (n + 1)}
    (a : LieBondField (doubleBlockSymmetricSet c)) : BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  fun b => (a.eval b : Matrices.ComplexMatrix2)
def StepCurvatureGrowth : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L →
    IsCurvatureGrowthPair L (curvatureGrowthConst L) (curvatureGrowthRadius L) ∧
    ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (c : BondAtLevel L m K (n + 1)),
      c.IsPositivelyOriented →
      ∀ a : LieBondField (doubleBlockSymmetricSet c),
        HasDerivAt (fun t : ℂ => blockAverageLog s c (t • a))
          (linearSchemeBlockAverage s (matrixValues a) c) 0 ∧
        linearSchemeBlockAverage .centred (matrixValues a) c =
          scaledLinearBlockAverage (matrixValues a) c ∧
        ∀ y ∈ bondEndpoints c, ∀ x ∈ sitesInBlock (levelDepth K n) y,
          HasDerivAt (fun t : ℂ => contourHolonomy s (expBondField c (t • a)) y x)
            (Complex.I • contourFormMean s (matrixValues a) y x) 0
end YangMills.Construction.PeriodicLattice
