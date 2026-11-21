import YangMills.Construction.Lattice.AveragesOfAConfigurationOnARegion
import YangMills.Construction.Lattice.BlockAxialGaugeOutsideTheNodes
import YangMills.Construction.Lattice.InwardBondsAndSetsInForce
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
open Matrices
variable {L m : ℕ}
structure IsAxialGaugeSetting (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (Y : Set (SiteAtLevel L m K (k + 1))) :
    Prop where
  succ_le : k + 1 ≤ K
  chain : IsDeterminingChain K (k + 1) Ω
  linkDatum : IsLinkDatum (activeBondSet K (k + 1) Ω) V
  uniqueOrbit :
    HasUniqueCriticalOrbit (Averaging.smoothingRadius L) ε K (k + 1) Ω (activeBondSet K (k + 1) Ω) V
  subset_sites : Y ⊆ sitesIn (Ω (k + 1))
  no_endpoints : ∀ x ∈ refinedBlockUnion 1 Y, (∀ y ∈ Y, x ≠ (y : FourTorus L m)) →
    ¬IsEndpointOf (activeBondSet K (k + 1) Ω) x
def chainCriticalSet (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  regularConstrainedCriticalSet (Averaging.smoothingRadius L) ε K (k + 1) Ω
    (activeBondSet K (k + 1) Ω) V
def axialGaugeRepresentatives (ε : ℝ) (K k : ℕ) (Ω : ℕ → Set (FourTorus L m))
    (V : ∀ j : ℕ, BondAtLevel L m K j → ComplexMatrix2) (Y : Set (SiteAtLevel L m K (k + 1))) :
    Set (BondAtLevel L m K 0 → ComplexMatrix2) :=
  {U | U ∈ chainCriticalSet ε K k Ω V ∧
    IsBlockAxialGauge K k Y (regionBlockField k (Ω 0) U)}
def blockAndEndpointSites {K k : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (Y : Set (SiteAtLevel L m K (k + 1))) : Set (SiteAtLevel L m K k) :=
  {x | (x : FourTorus L m) ∈ refinedBlockUnion 1 Y} ∪ endpointSitesAt B k
def blockAndEndpointBonds {K k : ℕ} (B : Set (Σ j : ℕ, BondAtLevel L m K j))
    (Y : Set (SiteAtLevel L m K (k + 1))) : Set (BondAtLevel L m K k) :=
  {c | c.source ∈ blockAndEndpointSites B Y ∧ c.target ∈ blockAndEndpointSites B Y}
end YangMills.Construction.PeriodicLattice
