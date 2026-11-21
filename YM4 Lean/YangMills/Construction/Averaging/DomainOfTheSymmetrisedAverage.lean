import YangMills.Construction.Lattice.InvertibleContourVariables
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Averaging
open Matrices PeriodicLattice
structure SymmetrisedDomainPropertiesAtBond {L m K : ℕ} (ω : ℝ) (k : ℕ)
    (c : BondAtLevel L m K (k + 1)) : Prop where
  exactlyOneMean : ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
    ∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
      ∀ x ∈ sitesInBlock (levelDepth K k) y, HasContourMean U y x
  dependAnalytically : ∀ _ : Fintype (PositivelyOrientedBond L m (levelDepth K k)),
    ContourMeansAnalyticOn ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1)))
      (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2))
  withinOne : c.IsPositivelyOriented →
    ∀ U ∈ (smallPlaquetteFields ω c : Set (BondAtLevel L m K k → ComplexMatrix2)),
      ∀ x ∈ sitesInBlock (levelDepth K k) c.source, IsNearIdentity (crossingDefect U c x)
def SymmetrisedDomainProperties (L m K : ℕ) (ω : ℝ) : Prop :=
  ∀ k, k < K → ∀ c : BondAtLevel L m K (k + 1), SymmetrisedDomainPropertiesAtBond ω k c
end YangMills.Construction.Averaging
end
