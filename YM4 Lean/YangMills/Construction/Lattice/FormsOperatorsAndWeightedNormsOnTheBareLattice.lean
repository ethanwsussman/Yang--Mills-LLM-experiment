import YangMills.Construction.Lattice.CovariantSiteOperators
import YangMills.Construction.Lattice.LieValuedBondFunctions
import YangMills.Construction.Lattice.SeparatedSequencesInLevelUnits
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Set PeriodicLattice Matrices
namespace SeparatedSequence
namespace DepthChain
variable {L m : ℕ} {N : DepthParameters L m} (A : DepthChain N)
abbrev gaugeFields : Set (BondAtLevel L m N.K 0 → ComplexMatrix2) :=
  gaugeFieldsInside N.K (A.region 0)
def baseSites : Set (SiteAtLevel L m N.K 0) := sitesIn (A.region 0)
def orientedBaseBonds : Set (BondAtLevel L m N.K 0) :=
  {b | b ∈ (bondsInside (A.region 0) : Set (BondAtLevel L m N.K 0)) ∧ b.IsPositivelyOriented}
def basePlaquettes : Set (PlaquetteAtLevel L m N.K 0) := plaquettesInside (A.region 0)
def siteFields (𝔥 : Set ComplexMatrix2) : Set (SiteAtLevel L m N.K 0 → ComplexMatrix2) :=
  {f | IsSiteField 𝔥 f ∧ zeroExtendSiteField (A.region 0) f = f}
def bondForms (𝔥 : Set ComplexMatrix2) : Set (BondAtLevel L m N.K 0 → ComplexMatrix2) :=
  {a | IsBondForm 𝔥 a ∧ (bondsInside (A.region 0)).indicator a = a}
def plaquetteForms (𝔥 : Set ComplexMatrix2) : Set (PlaquetteAtLevel L m N.K 0 → ComplexMatrix2) :=
  {X | (∀ p, X p ∈ 𝔥) ∧ (plaquettesInside (A.region 0)).indicator X = X}
def covGradient (U : BondAtLevel L m N.K 0 → ComplexMatrix2) (f : SiteAtLevel L m N.K 0 → ComplexMatrix2) :
    BondAtLevel L m N.K 0 → ComplexMatrix2 :=
  (bondsInside (A.region 0)).indicator (bondFormOfPositive fun b =>
    ((N.eta⁻¹ : ℝ) : ℂ) • (ComplexMatrix2.conjugateBy (U b) (f b.target) - f b.source))
def covCurl (U a : BondAtLevel L m N.K 0 → ComplexMatrix2) : PlaquetteAtLevel L m N.K 0 → ComplexMatrix2 :=
  (plaquettesInside (A.region 0)).indicator fun p =>
    covExteriorDeriv N.eta U a p.firstAxis p.secondAxis p.origin
def siteInner (f f' : SiteAtLevel L m N.K 0 → ComplexMatrix2) : ℂ :=
  ((N.eta ^ 4 : ℝ) : ℂ) * ∑ᶠ x ∈ A.baseSites, halfTracePairing (f x) (f' x)
def bondInner (a a' : BondAtLevel L m N.K 0 → ComplexMatrix2) : ℂ :=
  ((N.eta ^ 4 : ℝ) : ℂ) * ∑ᶠ b ∈ A.orientedBaseBonds, halfTracePairing (a b) (a' b)
def plaquetteInner (X X' : PlaquetteAtLevel L m N.K 0 → ComplexMatrix2) : ℂ :=
  ((N.eta ^ 4 : ℝ) : ℂ) * ∑ᶠ p ∈ A.basePlaquettes, halfTracePairing (X p) (X' p)
def covDivergence (𝔥 : Set ComplexMatrix2) (U a : BondAtLevel L m N.K 0 → ComplexMatrix2) :
    SiteAtLevel L m N.K 0 → ComplexMatrix2 :=
  Classical.epsilon fun B => B ∈ A.siteFields 𝔥 ∧ ∀ f ∈ A.siteFields 𝔥,
    A.siteInner B f = A.bondInner a (A.covGradient U f)
def covCurlAdjoint (𝔥 : Set ComplexMatrix2) (U : BondAtLevel L m N.K 0 → ComplexMatrix2)
    (X : PlaquetteAtLevel L m N.K 0 → ComplexMatrix2) : BondAtLevel L m N.K 0 → ComplexMatrix2 :=
  Classical.epsilon fun B => B ∈ A.bondForms 𝔥 ∧ ∀ a ∈ A.bondForms 𝔥,
    A.bondInner B a = A.plaquetteInner X (A.covCurl U a)
end DepthChain
end SeparatedSequence
end YangMills.Construction
