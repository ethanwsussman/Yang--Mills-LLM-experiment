import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.IsometryGroupsOfTheTorus
import YangMills.Construction.Lattice.LocalizationDomainsAndEdgeTrees
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ}
namespace IsometryInvariance
def MapsBlocks (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  ∀ (n : ℕ) (y : Site L m j), σ '' refinedBlock n y = refinedBlock n (sitePreimage σ.symm y)
def MapsAxialPaths (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  ∀ x x' : Site L m j, (∃ μ n, IsAxialDisplacement x x' μ n) →
    (∃ μ n, IsAxialDisplacement (sitePreimage σ.symm x) (sitePreimage σ.symm x') μ n) ∧
      pathImage σ (axialPath x x') =
        axialPath (sitePreimage σ.symm x) (sitePreimage σ.symm x')
def MapsContourSets (σ : FourTorus L m ≃ FourTorus L m) (j : ℤ) : Prop :=
  ∀ (y : Site L m j) (x : Site L m (j + 1)), (x : FourTorus L m) ∈ unitBlock y →
    pathImage σ '' contourSet y x =
      contourSet (sitePreimage σ.symm y) (sitePreimage σ.symm x)
def MapsBondObjects (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (k + 1),
    σ '' bondDoubleBlock c = bondDoubleBlock (bondImage σ c) ∧
    bondImage σ '' (bondCorridor c : Set (BondAtLevel L m K k)) = bondCorridor (bondImage σ c) ∧
    bondImage σ (pivot c : BondAtLevel L m K k) = pivot (bondImage σ c) ∧
    bondImage σ ''
        (bondsInDoubleBlock c.positivelyOriented : Set (BondAtLevel L m K k)) =
      bondsInDoubleBlock (bondImage σ c).positivelyOriented
def MapsSitesIn (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ) (X : Set (FourTorus L m)) : Prop :=
  (sitePreimage σ.symm) '' (sitesIn X : Set (SiteAtLevel L m K k)) = sitesIn (σ '' X)
def MapsNonPivotBonds (σ : FourTorus L m ≃ FourTorus L m) (K k : ℕ) (X : Set (FourTorus L m)) :
    Prop :=
  bondImage σ '' nonPivotBonds K k X = nonPivotBonds K k (σ '' X)
def MapsEdgeGraphs (σ : FourTorus L m ≃ FourTorus L m) (K m' j : ℕ) : Prop :=
  ∀ X, IsPartitionRegion (coarseCubeIndex K m' j) X →
    (fun Γ => σ '' Γ) '' {Γ | IsEdgeGraph (coarseCubeIndex K m' j) X Γ} =
        {Γ | IsEdgeGraph (coarseCubeIndex K m' j) (σ '' X) Γ} ∧
      ∀ Γ, IsEdgeGraph (coarseCubeIndex K m' j) X Γ →
        graphLength (L ^ m') (coarseCubeIndex K m' j) (σ '' Γ) =
          graphLength (L ^ m') (coarseCubeIndex K m' j) Γ
def MapsConnectedRegions (σ : FourTorus L m ≃ FourTorus L m) (K m' j : ℕ) : Prop :=
  (fun X => σ '' X) '' connectedRegions L m (coarseCubeIndex K m' j) =
      connectedRegions L m (coarseCubeIndex K m' j) ∧
    ∀ X ∈ connectedRegions L m (coarseCubeIndex K m' j),
      linearExtent K m' j (σ '' X) = linearExtent K m' j X ∧
        ∀ Z, IsPartitionRegion (coarseCubeIndex K m' j) Z →
          relativeLinearExtent K m' j (σ '' Z) (σ '' X) = relativeLinearExtent K m' j Z X
def MapsIslandExtents (σ : FourTorus L m ≃ FourTorus L m) (K m' j : ℕ) : Prop :=
  ∀ I, IsIslandCollection (coarseCubeIndex K m' j) I →
    IsIslandCollection (coarseCubeIndex K m' j) ((fun B => σ '' B) '' I) ∧
      (fun X => σ '' X) '' islandRegions (coarseCubeIndex K m' j) I =
        islandRegions (coarseCubeIndex K m' j) ((fun B => σ '' B) '' I) ∧
      ∀ X ∈ islandRegions (coarseCubeIndex K m' j) I,
        islandLinearExtent K m' j ((fun B => σ '' B) '' I) (σ '' X) = islandLinearExtent K m' j I X
def InvariantUnderIsometries : Prop :=
  ∀ L m : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
  ∀ i : ℤ, -(m : ℤ) ≤ i → ∀ σ ∈ latticeIsometries L m i,
    (∀ j : ℤ, i ≤ j →
      MapsBlocks σ j ∧ MapsAxialPaths σ j ∧ MapsContourSets σ j) ∧
    (∀ K k : ℕ, k < K → i ≤ levelDepth K (k + 1) → MapsBondObjects σ K k) ∧
    (∀ K k : ℕ, k ≤ K → ∀ i' : ℤ, i ≤ i' → i' ≤ levelDepth K k →
      ∀ X, IsPartitionRegion i' X → MapsSitesIn σ K k X) ∧
    (∀ K k : ℕ, k < K → i ≤ levelDepth K (k + 1) → ∀ i' : ℤ, i ≤ i' → i' ≤ levelDepth K k →
      ∀ X, IsPartitionRegion i' X → MapsNonPivotBonds σ K k X) ∧
    (∀ K m' j : ℕ, j ≤ K → i ≤ coarseCubeIndex K m' j →
      MapsEdgeGraphs σ K m' j ∧ MapsConnectedRegions σ K m' j ∧
        MapsIslandExtents σ K m' j)
end IsometryInvariance
end YangMills.Construction.PeriodicLattice
