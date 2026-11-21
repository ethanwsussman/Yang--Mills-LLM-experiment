import YangMills.Construction.Lattice.AxialGauges
import YangMills.Construction.Lattice.LandauGaugeRelativeToABackground
import Mathlib
set_option autoImplicit false
open Set Filter Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
namespace YangMills.Construction
open Matrices
namespace PeriodicLattice.FrameForms
section Averages
variable {L m : ℕ} {j j' : ℤ}
def combFromCoarse (r : SignedFrame) (z : Site L m j) (x : Site L m j') : List (Bond L m j') :=
  rotatedComb r (z.toSublattice j') x
def combHolonomyRot (r : SignedFrame) (W : Bond L m j' → ComplexMatrix2) (z : Site L m j)
    (x : Site L m j') : ComplexMatrix2 :=
  pathHolonomy W (combFromCoarse r z x)
def logArgRot (r : SignedFrame) (W : Bond L m j' → ComplexMatrix2)
    (v : Site L m j' → ComplexMatrix2) (z : Site L m j) (x : Site L m j') : ComplexMatrix2 :=
  (v (z.toSublattice j'))⁻¹ * ComplexMatrix2.conjugateBy (combHolonomyRot r W z x) (v x)
def StepAverageDefinedRot (r : SignedFrame) (W : Bond L m j' → ComplexMatrix2)
    (v : Site L m j' → ComplexMatrix2) (z : Site L m j) : Prop :=
  ∀ x ∈ sitesInBlock j' z, logArgRot r W v z x ∈ ComplexMatrix2.logBall
def stepAverageRot (r : SignedFrame) (W : Bond L m j' → ComplexMatrix2)
    (v : Site L m j' → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  fun z => v (z.toSublattice j') * ComplexMatrix2.matExp (inverseFourthPowerWeight L •
    ∑ᶠ x ∈ sitesInBlock j' z, ComplexMatrix2.logSeries (logArgRot r W v z x))
def stepLinearAverageRot (r : SignedFrame) (W : Bond L m j' → ComplexMatrix2)
    (f : Site L m j' → ComplexMatrix2) : Site L m j → ComplexMatrix2 :=
  fun z => inverseFourthPowerWeight L •
    ∑ᶠ x ∈ sitesInBlock j' z, ComplexMatrix2.conjugateBy (combHolonomyRot r W z x) (f x)
variable {K : ℕ}
def iteratedAverageRot (r : SignedFrame) (I : BlockingIterates L m K)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → ComplexMatrix2
  | 0, v => v
  | n + 1, v => stepAverageRot r (I.value n U) (iteratedAverageRot r I U n v)
def IteratedAverageDefinedRot (r : SignedFrame) (I : BlockingIterates L m K)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → Prop
  | 0, _, _ => True
  | n + 1, v, z =>
    (∀ x ∈ sitesInBlock (levelDepth K n) z, IteratedAverageDefinedRot r I U n v x) ∧
      StepAverageDefinedRot r (I.value n U) (iteratedAverageRot r I U n v) z
def IsAverageNormalizedRot (r : SignedFrame) (I : BlockingIterates L m K) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2)
    (v : SiteAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  ∀ i ≤ k, ∀ y ∈ annulusSites K k Ω i,
    IteratedAverageDefinedRot r I U i v y ∧ iteratedAverageRot r I U i v y = 1
def iteratedLinearAverageRot (r : SignedFrame) (I : BlockingIterates L m K)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (n : ℕ) → (SiteAtLevel L m K 0 → ComplexMatrix2) → SiteAtLevel L m K n → ComplexMatrix2
  | 0, f => f
  | n + 1, f => stepLinearAverageRot r (I.value n U) (iteratedLinearAverageRot r I U n f)
def admissibleGaugesRot (r : SignedFrame) (I : BlockingIterates L m K) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    Set (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  {f | IsSiteField complexLieAlgebra f ∧ zeroExtendSiteField (Ω 0) f = f ∧
    ∀ i ≤ k, ∀ y ∈ annulusSites K k Ω i, iteratedLinearAverageRot r I U i f y = 0}
def extendByOne (X : Set (FourTorus L m)) (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  fun b => open Classical in
    if b ∈ (bondsInside X : Set (BondAtLevel L m K 0)) then U₀ b else 1
def extendByZero (X : Set (FourTorus L m)) (A : BondAtLevel L m K 0 → ComplexMatrix2) :
    BondAtLevel L m K 0 → ComplexMatrix2 :=
  (bondsInside X : Set (BondAtLevel L m K 0)).indicator A
def landauImageRot (r : SignedFrame) (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) : Set (SiteAtLevel L m K 0 → ComplexMatrix2) :=
  covLaplacian (Ω 0) ξ (extendByOne (Ω 0) U₀) ''
    (admissibleGaugesRot r (realBlockingIterates ω) k Ω U₀ ∩ realSiteFieldsSupportedIn (Ω 0))
def landauProjectionRealRot (r : SignedFrame) (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) (f : SiteAtLevel L m K 0 → ComplexMatrix2) :
    SiteAtLevel L m K 0 → ComplexMatrix2 :=
  Classical.epsilon fun g => g ∈ landauImageRot r ω ξ k Ω U₀ ∧
    ∀ w ∈ landauImageRot r ω ξ k Ω U₀, siteInner ξ (f - g) w = 0
def landauProjectorRot (r : SignedFrame) (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ : BondAtLevel L m K 0 → ComplexMatrix2) (f : SiteAtLevel L m K 0 → ComplexMatrix2) :
    SiteAtLevel L m K 0 → ComplexMatrix2 :=
  landauProjectionRealRot r ω ξ k Ω U₀ (siteFieldRe f) +
    Complex.I • landauProjectionRealRot r ω ξ k Ω U₀ (siteFieldIm f)
def SatisfiesLandauGaugeRot (r : SignedFrame) (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ A : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  landauProjectorRot r ω ξ k Ω U₀
    (covDivergence (Ω 0) ξ (extendByOne (Ω 0) U₀) (extendByZero (Ω 0) A)) = 0
def IsLandauPairRot (r : SignedFrame) (ω ξ : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U A : BondAtLevel L m K 0 → ComplexMatrix2) (u : SiteAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  IsRealBondFormOn (bondsInside (Ω 0)) A ∧ IsGaugeTransformSupportedIn (Ω 0) u ∧
    (∀ b ∈ (bondsInside (Ω 0) : Set (BondAtLevel L m K 0)),
      U b = gaugeTransform u (expTwist (meshScaledForm ξ A) U₀) b) ∧
    SatisfiesLandauGaugeRot r ω ξ k Ω U₀ A ∧
    IsAverageNormalizedRot r (realBlockingIterates ω) k Ω U₀ u
def IsSmallFieldLandauPairRot (r : SignedFrame) (ω ξ α : ℝ) (k : ℕ)
    (Ω : ℕ → Set (FourTorus L m)) (U₀ U : BondAtLevel L m K 0 → ComplexMatrix2)
    (p : (BondAtLevel L m K 0 → ComplexMatrix2) × (SiteAtLevel L m K 0 → ComplexMatrix2)) :
    Prop :=
  IsLandauPairRot r ω ξ k Ω U₀ U p.1 p.2 ∧ IsLandauSmallField ξ α k Ω U₀ p.1
def landauGaugeFormRot (r : SignedFrame) (ω ξ α : ℝ) (k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (U₀ U : BondAtLevel L m K 0 → ComplexMatrix2) : BondAtLevel L m K 0 → ComplexMatrix2 :=
  (Classical.epsilon (IsSmallFieldLandauPairRot r ω ξ α k Ω U₀ U)).1
end Averages
end PeriodicLattice.FrameForms
end YangMills.Construction
