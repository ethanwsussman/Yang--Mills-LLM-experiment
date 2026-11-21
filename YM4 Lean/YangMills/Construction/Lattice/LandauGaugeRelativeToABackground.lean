import YangMills.Construction.Lattice.GaugeAverages
import YangMills.Construction.Lattice.RegularAtRadius
import Mathlib
set_option autoImplicit false
open Set Filter Topology YangMills.Construction.Matrices
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ} {j : ℤ}
def regularFieldsOnChain (r : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m)) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {U | U ∈ gaugeFieldsInside K (Ω 0) ∧ IsRegularWithRadius r K k Ω U}
structure IsLandauBackground (ω ξ α₀ : ℝ) (K k e r : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) : Prop where
  level_le : k ≤ K
  mesh_pos : 0 < ξ
  chain : IsDeterminingChain K k Ω
  separated : IsSeparatedChain K e r 0 k Ω
  regular : U₀ ∈ regularFieldsOnChain α₀ K k Ω
  blocking_defined : ∀ n ≤ k, ∀ c : BondAtLevel L m K n, EndpointBlocksSubset (Ω 0) n c →
    (realBlockingIterates ω).IsDefinedAt n U₀ c
def realSiteFieldsSupportedIn (X : Set (FourTorus L m)) : Set (Site L m j → ComplexMatrix2) :=
  {f | IsSiteField compactLieAlgebra f ∧ zeroExtendSiteField X f = f}
def landauLaplacianImage (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) : Set (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  covLaplacian (Ω 0) ξ U₀ ''
    (admissibleInfinitesimalGauges (realBlockingIterates ω) k Ω U₀ ∩
      realSiteFieldsSupportedIn (Ω 0))
def landauProjectionReal (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) (f : SiteAtLevel L m K 0 → ComplexMatrix2) :
    SiteAtLevel L m K 0 → ComplexMatrix2 :=
  Classical.epsilon fun g => g ∈ landauLaplacianImage ω ξ k Ω U₀ ∧
    ∀ w ∈ landauLaplacianImage ω ξ k Ω U₀, siteInner ξ (f - g) w = 0
def siteFieldRe (f : Site L m j → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  fun x => (2⁻¹ : ℂ) • (f x + (f x).conjTranspose)
def siteFieldIm (f : Site L m j → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  fun x => (2 * Complex.I)⁻¹ • (f x - (f x).conjTranspose)
def landauProjector (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) (f : SiteAtLevel L m K 0 → ComplexMatrix2) :
    SiteAtLevel L m K 0 → ComplexMatrix2 :=
  landauProjectionReal ω ξ k Ω U₀ (siteFieldRe f) +
    Complex.I • landauProjectionReal ω ξ k Ω U₀ (siteFieldIm f)
def SatisfiesLandauGauge (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  landauProjector ω ξ k Ω U₀ (covDivergence (Ω 0) ξ U₀ A) = 0
def IsRealBondFormOn (ℬ : Set (Bond L m j)) (A : Bond L m j → ComplexMatrix2) : Prop :=
  IsBondForm compactLieAlgebra A ∧ ℬ.indicator A = A
def IsGaugeTransformSupportedIn (X : Set (FourTorus L m)) (u : Site L m j → ComplexMatrix2) :
    Prop :=
  (∀ x ∈ (sitesIn X : Set (Site L m j)), u x ∈ compactGaugeGroup) ∧
    ∀ x ∉ (sitesIn X : Set (Site L m j)), u x = 1
def meshScaledForm (ξ : ℝ) (A : Bond L m j → ComplexMatrix2) : Bond L m j → ComplexMatrix2 :=
  ((ξ : ℝ) : ℂ) • A
def IsLandauPair (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U A : BondAtLevel L m K 0 → ComplexMatrix2) (u : SiteAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  IsRealBondFormOn (bondsInside (Ω 0)) A ∧ IsGaugeTransformSupportedIn (Ω 0) u ∧
    (∀ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
      U b = gaugeTransform u (expTwist (meshScaledForm ξ A) U₀) b) ∧
    SatisfiesLandauGauge ω ξ k Ω U₀ A ∧
    IsAverageNormalized (realBlockingIterates ω) k Ω U₀ u
def landauShell (k : ℕ) (Ω : ℕ → Set (FourTorus L m)) (j : ℕ) : Set (FourTorus L m) :=
  if j < k then Ω j \ Ω (j + 1) else Ω k
def CovDerivBondsInside (X : Set (FourTorus L m)) (x : Site L m j) (μ ν : Fin 4) : Prop :=
  Bond.forwardFrom x μ ∈ (bondsInside X : Set (Bond L m j)) ∧
    Bond.forwardFrom x ν ∈ (bondsInside X : Set (Bond L m j)) ∧
    Bond.forwardFrom (x + unitStep L m j μ) ν ∈ (bondsInside X : Set (Bond L m j))
def IsLandauSmallField (ξ α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ j ≤ k,
    (∀ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
      b ∈ (bondsMeeting (landauShell k Ω j) : Set (BondAtLevel L m K 0)) →
        (L : ℝ) ^ j * ξ * ComplexMatrix2.operatorNorm (A b) < α) ∧
    ∀ x ∈ (sitesIn (landauShell k Ω j) : Set (SiteAtLevel L m K 0)), ∀ μ ν : Fin 4,
      CovDerivBondsInside (Ω 0) x μ ν →
        ((L : ℝ) ^ j * ξ) ^ 2 *
          ComplexMatrix2.operatorNorm (covDeriv ξ U₀ μ (bondFormComponent A ν) x) < α
def IsSmallFieldLandauPair (ω ξ α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U : BondAtLevel L m K 0 → ComplexMatrix2)
    (p : (BondAtLevel L m K 0 → ComplexMatrix2) × (SiteAtLevel L m K 0 → ComplexMatrix2)) :
    Prop :=
  IsLandauPair ω ξ k Ω U₀ U p.1 p.2 ∧ IsLandauSmallField ξ α k Ω U₀ p.1
def ExistsUniqueSmallFieldLandauPair (ω ξ α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∃! p, IsSmallFieldLandauPair ω ξ α k Ω U₀ U p
def landauGaugeForm (ω ξ α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U : BondAtLevel L m K 0 → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  (Classical.epsilon (IsSmallFieldLandauPair ω ξ α k Ω U₀ U)).1
def wilsonHessian (ξ : ℝ) (K : ℕ) (X : Set (FourTorus L m))
    (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => actionInside K X (expTwist (((t * ξ : ℝ) : ℂ) • A) U₀)) 0
end PeriodicLattice
end YangMills.Construction
