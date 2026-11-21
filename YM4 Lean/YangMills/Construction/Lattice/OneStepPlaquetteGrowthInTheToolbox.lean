import YangMills.Construction.Lattice.BondsWithinSiteSets
import YangMills.Construction.Lattice.OneStepCovarianceAndDomainsInTheToolbox
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m K n : ℕ}
def plaquetteBlockSites (p : PlaquetteAtLevel L m K (n + 1)) : Set (SiteAtLevel L m K n) :=
  sitesIn (refinedBlockUnion 1 p.vertices)
structure IsPlaquetteGrowthPair (L : ℕ) (C ϖ' : ℝ) : Prop where
  one_le : 1 ≤ C
  pos : 0 < ϖ'
  le_bound : ϖ' ≤ plaquetteSmallness L
  growth : ∀ m K n : ℕ, 0 < m → n < K → ∀ (s : AveragingScheme) (p : PlaquetteAtLevel L m K (n + 1))
    (W : BondAtLevel L m K n → Matrices.ComplexMatrix2),
    IsGaugeFieldWithin (plaquetteBlockSites p) W →
    maxPlaquetteDeviation (plaquetteBlockSites p) W ≤ ϖ' →
      Matrices.ComplexMatrix2.operatorNorm (plaquetteHolonomy (oneStepAverage s W) p - 1) ≤
        (L : ℝ) ^ 2 * maxPlaquetteDeviation (plaquetteBlockSites p) W +
          C * maxPlaquetteDeviation (plaquetteBlockSites p) W ^ 2
def plaquetteGrowthPair (L : ℕ) : ℝ × ℝ :=
  Classical.epsilon fun p => IsPlaquetteGrowthPair L p.1 p.2
def plaquetteGrowthConstant (L : ℕ) : ℝ := (plaquetteGrowthPair L).1
def plaquetteGrowthRadius (L : ℕ) : ℝ := (plaquetteGrowthPair L).2
def linearStepAverage {j j' : ℤ} (s : AveragingScheme) (a : Bond L m j' → Matrices.ComplexMatrix2)
    (c : Bond L m j) : Matrices.ComplexMatrix2 :=
  inverseFourthPowerWeight L • ∑ᶠ x ∈ sitesInBlock j' c.source, (contourFormMean s a c.source x +
    bondFormSumAlong a (crossingPath c x) - contourFormMean s a c.target (shiftAcross c x))
def lieFieldMatrices {c : BondAtLevel L m K (n + 1)}
    (a : LieBondField (doubleBlockSymmetricSet c)) : BondAtLevel L m K n → Matrices.ComplexMatrix2 :=
  fun b => (a.eval b : Matrices.ComplexMatrix2)
end YangMills.Construction.PeriodicLattice
