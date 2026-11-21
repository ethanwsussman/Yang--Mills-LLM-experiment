import YangMills.Construction.Lattice.AveragesAndPropagatorsAtAConfiguration
import YangMills.Construction.Lattice.MatrixValuedForms
import YangMills.Construction.Lattice.SequencesAtACubeSizeAndAGap
import YangMills.Construction.Lattice.UnitsAndSpacesOfConfigurations
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open Matrices BondMaps Conventions PeriodicLattice
namespace PeriodicLattice
variable {L m K : ℕ}
def IsPosDefOn {V : Type*} [Zero V] (S : Set V) (p : V → V → ℂ) (T : V → V) : Prop :=
  Set.MapsTo T S S ∧ (∀ f ∈ S, ∀ g ∈ S, p (T f) g = p f (T g)) ∧
    ∀ f ∈ S, f ≠ 0 → ∃ t : ℝ, 0 < t ∧ p f (T f) = (t : ℂ)
def expDecayBound {k : ℕ} (B δ : ℝ) (y y' : SiteAtLevel L m K k) : ℝ :=
  B * Real.exp (-δ * supNormDistInLevelScale L m K k (y : FourTorus L m) (y' : FourTorus L m))
def covDerivLocalSup {k : ℕ} (y : SiteAtLevel L m K k) (U A : BondAtLevel L m K 0 → ComplexMatrix2) :
    ℝ :=
  ⨆ x : ↥(blockSitesAtLevel 0 y), covDerivNorm (finestMeshInLevelUnits L k) U A x
def MassiveSitePropagatorDecay (B δ : ℝ) (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  IsPosDefOn (compactBareSiteFields L m K) (siteInner (finestMeshInLevelUnits L k))
      (massiveSiteLaplacian k U) ∧
    ∀ y y' : SiteAtLevel L m K k, ∀ f ∈ compactBareSiteFields L m K, SiteFieldSupportedOver y' f →
      siteLocalSup y (massiveSitePropagator k U f) ≤ expDecayBound B δ y y' * supOfOperatorNorms f ∧
        bondLocalSup y (bareCovGradient k U (massiveSitePropagator k U f)) ≤
          expDecayBound B δ y y' * supOfOperatorNorms f
def IsSiteKernel {k : ℕ}
    (T : (SiteAtLevel L m K k → ComplexMatrix2) → SiteAtLevel L m K k → ComplexMatrix2)
    (κ : SiteAtLevel L m K k → SiteAtLevel L m K k →
      (ComplexMatrix2.hermitianTraceless →ₗ[ℝ] ComplexMatrix2.hermitianTraceless)) : Prop :=
  ∀ (μ : SiteAtLevel L m K k → ComplexMatrix2.hermitianTraceless) (y : SiteAtLevel L m K k),
    T (fun z => (μ z : ComplexMatrix2)) y = ∑ᶠ y', (κ y y' (μ y') : ComplexMatrix2)
def averagedSquaredPropagatorInv (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    (SiteAtLevel L m K k → ComplexMatrix2) → SiteAtLevel L m K k → ComplexMatrix2 :=
  inverseOn (compactSiteFieldsAtLevel L m K k) (averagedSquaredPropagator k U)
def AveragedPropagatorInvDecay (B δ : ℝ) (k : ℕ) (U : BondAtLevel L m K 0 → ComplexMatrix2) :
    Prop :=
  IsPosDefOn (compactSiteFieldsAtLevel L m K k) siteInnerAtLevel
      (averagedSquaredPropagator k U) ∧
    ∃ κ, IsSiteKernel (averagedSquaredPropagatorInv k U) κ ∧
      ∀ (y y' : SiteAtLevel L m K k) (v : ComplexMatrix2.hermitianTraceless),
        ComplexMatrix2.operatorNorm (κ y y' v : ComplexMatrix2) ≤
          expDecayBound B δ y y' * ComplexMatrix2.operatorNorm (v : ComplexMatrix2)
def GaugeFixedPropagatorDecay [∀ n, Fintype (PositiveBondAtLevel L m K n)] (B δ : ℝ) (k : ℕ)
    (U : BondAtLevel L m K 0 → ComplexMatrix2) : Prop :=
  IsPosDefOn (compactBareBondForms L m K) (bondFormInner (finestMeshInLevelUnits L k))
      (gaugeFixedHessian k U) ∧
    ∀ y y' : SiteAtLevel L m K k, ∀ f ∈ compactBareBondForms L m K, BondFieldSupportedOver y' f →
      bondLocalSup y (gaugeFixedPropagator k U f) ≤ expDecayBound B δ y y' * supOfOperatorNorms f ∧
        covDerivLocalSup y U (gaugeFixedPropagator k U f) ≤
          expDecayBound B δ y y' * supOfOperatorNorms f
def GlobalPropagatorBounds (L : ℕ) (B δ a r : ℝ) : Prop :=
  ∀ K m k : ℕ, 1 ≤ m → 1 ≤ k → k ≤ K →
    6 * r ≤ RegionChains.sitesPerAxis L m K k →
    ∀ α : ℝ, 0 < α → α ≤ a → ∀ U ∈ smallCurvatureConfigsAtLevel L m K k α,
      MassiveSitePropagatorDecay B δ k U ∧ AveragedPropagatorInvDecay B δ k U ∧
        ∀ _ : ∀ n, Fintype (PositiveBondAtLevel L m K n), GaugeFixedPropagatorDecay B δ k U
end PeriodicLattice
end YangMills.Construction
