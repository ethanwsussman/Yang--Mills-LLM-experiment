import YangMills.Construction.Lattice.AssertionsOfTheStraightenedAverageOfOrderK
import YangMills.Construction.Lattice.AveragingMassCoefficient
import YangMills.Construction.Lattice.BareLatticeSpacesAndOperators
import YangMills.Construction.Lattice.FirstVariationOfTheAction
import YangMills.Construction.Lattice.NumbersOfTheStraightenedAverage
import YangMills.Construction.Lattice.TowersOverSetsOfSites
import Mathlib
set_option autoImplicit false
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m K : ℕ}
structure IsPropagatorSetting (k : ℕ) (α : ℝ) (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop where
  one_le : 1 ≤ k
  le_levels : k ≤ K
  pos : 0 < α
  le_threshold : α ≤ straightenedCurvatureThreshold L
  mem_fields : U ∈ gaugeFieldsAtLevel L m K 0
  curvature_small : FinestCurvatureSmallOn k α U Set.univ
def blockCenterAt (j : ℕ) (x : SiteAtLevel L m K 0) : SiteAtLevel L m K j :=
  Classical.epsilon fun z : SiteAtLevel L m K j => x ∈ blockSitesAtLevel 0 z
def blockTransport (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (k : ℕ) → SiteAtLevel L m K k → SiteAtLevel L m K 0 → ComplexMatrix2
  | 0, _, _ => 1
  | 1, y, x => contourHolonomy .cornered (iteratedAverage .cornered 0 U) y x
  | n + 2, y, x =>
      contourHolonomy .cornered (iteratedAverage .cornered (n + 1) U) y (blockCenterAt (n + 1) x) *
        blockTransport U (n + 1) (blockCenterAt (n + 1) x) x
def siteBlockAverage (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m K 0 → ComplexMatrix2) : SiteAtLevel L m K k → ComplexMatrix2 :=
  fun y => (((L : ℝ) ^ (-(4 * (k : ℤ))) : ℝ) : ℂ) •
    ∑ᶠ x ∈ blockSitesAtLevel 0 y, ComplexMatrix2.conjugateBy (blockTransport U k y x) (f x)
def compactBareSiteFields (L m K : ℕ) : Set (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  {f | IsSiteField compactLieAlgebra f}
def compactBareBondForms (L m K : ℕ) : Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {A | IsBondForm compactLieAlgebra A}
def compactSiteFieldsAtLevel (L m K k : ℕ) : Set (SiteAtLevel L m K k → ComplexMatrix2) :=
  {μ | IsSiteField compactLieAlgebra μ}
def siteInnerAtLevel {k : ℕ} (μ ν : SiteAtLevel L m K k → ComplexMatrix2) : ℂ :=
  ∑ᶠ y, halfTracePairing (μ y) (ν y)
def bondInnerAtLevel {k : ℕ} (ω ω' : LieBondFunction L m (levelDepth K k)) : ℂ :=
  ∑ᶠ c, halfTracePairing (ω c : ComplexMatrix2) (ω' c : ComplexMatrix2)
def siteBlockAverageAdjoint (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (μ : SiteAtLevel L m K k → ComplexMatrix2) : SiteAtLevel L m K 0 → ComplexMatrix2 :=
  Bare.transposeWith (compactBareSiteFields L m K) (siteInner (finestMeshInLevelUnits L k))
    siteInnerAtLevel (siteBlockAverage k U) μ
def IsBijectiveOn {V : Type*} (S : Set V) (T : V → V) : Prop := Set.BijOn T S S
def inverseOn {V : Type*} [Nonempty V] (S : Set V) (T : V → V) (f : V) : V :=
  Classical.epsilon fun g => g ∈ S ∧ T g = f
def massiveSiteLaplacian (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m K 0 → ComplexMatrix2) : SiteAtLevel L m K 0 → ComplexMatrix2 :=
  covLaplacian Set.univ (finestMeshInLevelUnits L k) U f +
    ((Lattice.averagingMassCoefficient L k : ℝ) : ℂ) •
      siteBlockAverageAdjoint k U (siteBlockAverage k U f)
def massiveSitePropagator (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K 0 → ComplexMatrix2 :=
  inverseOn (compactBareSiteFields L m K) (massiveSiteLaplacian k U)
def averagedSquaredPropagator (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (μ : SiteAtLevel L m K k → ComplexMatrix2) : SiteAtLevel L m K k → ComplexMatrix2 :=
  siteBlockAverage k U (massiveSitePropagator k U
    (massiveSitePropagator k U (siteBlockAverageAdjoint k U μ)))
def propagatorProjection (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m K 0 → ComplexMatrix2) : SiteAtLevel L m K 0 → ComplexMatrix2 :=
  massiveSitePropagator k U (siteBlockAverageAdjoint k U
    (inverseOn (compactSiteFieldsAtLevel L m K k) (averagedSquaredPropagator k U)
      (siteBlockAverage k U (massiveSitePropagator k U f))))
def complementProjection (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (f : SiteAtLevel L m K 0 → ComplexMatrix2) : SiteAtLevel L m K 0 → ComplexMatrix2 :=
  f - propagatorProjection k U f
section BondForms
variable [∀ n, Fintype (PositiveBondAtLevel L m K n)]
def bondFormAverage (k : ℕ) (U A : BondAtLevel L m K 0 → ComplexMatrix2) :
    LieBondFunction L m (levelDepth K k) :=
  StraightenedOrder.linearizationAtOrder .cornered k U fun v => toTraceless (A v.1)
def bondFormAverageAdjoint (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (ω : LieBondFunction L m (levelDepth K k)) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  Bare.transposeWith (compactBareBondForms L m K) (bondFormInner (finestMeshInLevelUnits L k))
    bondInnerAtLevel (bondFormAverage k U) ω
def actionHessian (k : ℕ) (U A : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  bareCovExteriorDerivAdjoint k U (bareCovExteriorDeriv k U A) + gradientExpansionLinear k U A
def gaugeFixedHessian (k : ℕ) (U A : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  actionHessian k U A + bareCovGradient k U (complementProjection k U (bareCovDivergence k U A)) +
    bondFormAverageAdjoint k U (bondFormAverage k U A)
def gaugeFixedPropagator (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (BondAtLevel L m K 0 → ComplexMatrix2) → BondAtLevel L m K 0 → ComplexMatrix2 :=
  inverseOn (compactBareBondForms L m K) (gaugeFixedHessian k U)
end BondForms
section LocalSuprema
variable {k : ℕ}
def finestBondsOver (y : SiteAtLevel L m K k) : Set (BondAtLevel L m K 0) :=
  {v | v.IsPositivelyOriented ∧ v.source ∈ blockSitesAtLevel 0 y}
def siteLocalSup (y : SiteAtLevel L m K k) (f : SiteAtLevel L m K 0 → ComplexMatrix2) : ℝ :=
  supOfOperatorNorms fun x : ↥(blockSitesAtLevel 0 y) => f x
def bondLocalSup (y : SiteAtLevel L m K k) (f : BondAtLevel L m K 0 → ComplexMatrix2) : ℝ :=
  supOfOperatorNorms fun v : ↥(finestBondsOver y) => f v
def SiteFieldSupportedOver (y : SiteAtLevel L m K k) (f : SiteAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  ∀ x, x ∉ blockSitesAtLevel 0 y → f x = 0
def BondFieldSupportedOver (y : SiteAtLevel L m K k) (f : BondAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  ∀ v : BondAtLevel L m K 0, v.IsPositivelyOriented → v ∉ finestBondsOver y → f v = 0
end LocalSuprema
end YangMills.Construction.PeriodicLattice
