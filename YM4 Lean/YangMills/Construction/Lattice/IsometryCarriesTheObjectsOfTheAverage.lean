import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
namespace IsometryImages
variable {L m : ℕ} {j j' : ℤ}
def MapsBlockSites (σ : FourTorus L m ≃ FourTorus L m) (j' : ℤ) (y : Site L m j) : Prop :=
  BijOn (sitePreimage σ.symm) (sitesInBlock j' y) (sitesInBlock j' (sitePreimage σ.symm y))
def MapsContourIndices (σ : FourTorus L m ≃ FourTorus L m) (y : Site L m j) (x : Site L m j') :
    Prop :=
  ∃ e : AxisOrdering y x ≃ AxisOrdering (sitePreimage σ.symm y) (sitePreimage σ.symm x),
    ∀ s, orderedContour (sitePreimage σ.symm y) (sitePreimage σ.symm x) (e s) =
      pathImage σ (orderedContour y x s)
def MapsCrossing (σ : FourTorus L m ≃ FourTorus L m) (c : Bond L m j) (x : Site L m j') : Prop :=
  sitePreimage σ.symm (shiftAcross c x) =
      shiftAcross (bondImage σ c) (sitePreimage σ.symm x) ∧
    pathImage σ (crossingPath c x) = crossingPath (bondImage σ c) (sitePreimage σ.symm x)
def MapsTransportPath (σ : FourTorus L m ≃ FourTorus L m) (j' : ℤ) (c : Bond L m j) : Prop :=
  pathImage σ (axialPath (c.source.toSublattice j') (c.target.toSublattice j')) =
    axialPath ((bondImage σ c).source.toSublattice j') ((bondImage σ c).target.toSublattice j')
def MapsDoubleBlockPlaquettes (σ : FourTorus L m ≃ FourTorus L m) (j' : ℤ) (c : Bond L m j) :
    Prop :=
  plaquetteImage σ '' (doubleBlockPlaquettes c : Set (Plaquette L m j')) =
    doubleBlockPlaquettes (bondImage σ c)
def Statement : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ i : ℤ, -(m : ℤ) ≤ i → ∀ σ ∈ latticeIsometries L m i,
  ∀ j j' : ℤ, i ≤ j → 0 ≤ j → j' = j + 1 →
    (∀ y : Site L m j, MapsBlockSites σ j' y ∧
      ∀ x ∈ sitesInBlock j' y, MapsContourIndices σ y x) ∧
    ∀ c : Bond L m j, (∀ x : Site L m j', MapsCrossing σ c x) ∧
      MapsTransportPath σ j' c ∧ MapsDoubleBlockPlaquettes σ j' c
end IsometryImages
end PeriodicLattice
end YangMills.Construction
