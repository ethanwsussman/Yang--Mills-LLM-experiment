import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Lattice.BareDoubleBlocks
import YangMills.Construction.Lattice.BoxesOfSitesFromACorner
import YangMills.Construction.Lattice.PathsOfBlocksAndDoubleBlocks
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open Set TorusMetric Matrices
noncomputable section
namespace PeriodicLattice
variable {L m K : ℕ}
def regionBlockAverage (X : Set (FourTorus L m)) (U : BondAtLevel L m K 0 → ComplexMatrix2) (i : ℕ) :
    BondAtLevel L m K i → ComplexMatrix2 :=
  iterateFromBare
    (fun k W => blockAverageStep (Averaging.smoothingRadius L) k (extendByOne (bondsInside X) W)) i U
def SublatticesAndCubesInBareUnits (L m K : ℕ) : Prop :=
  toBareUnits L K (torusSide L m) = 2 * (L : ℝ) ^ (m + K) ∧
  (∀ q : ℕ, q ≤ K →
    toBareUnits L K (meshSize L (levelDepth K q)) = (L : ℝ) ^ q ∧
    (∀ (y : SiteAtLevel L m K q) (μ : Fin 4), (axisLine y μ).ncard = 2 * L ^ (m + K - q)) ∧
    2 * L ≤ 2 * L ^ (m + K - q) ∧
    ∀ i : ℕ, i ≤ q → sublattice L m (levelDepth K q) ≤ sublattice L m (levelDepth K i)) ∧
  ∀ q : ℕ, q ≤ K + 1 →
    -(m : ℤ) ≤ levelDepth K q ∧
    (∀ y : SiteAtLevel L m K q, cubeAround y =
      {x | toBareUnits L K (torusSupNorm (x - (y : FourTorus L m))) ≤ (L : ℝ) ^ q / 2}) ∧
    ⋃₀ cubePartitionOfSide L m K q = univ
def SitesInPartitionCubes (L m K i q : ℕ) : Prop :=
  ∀ x : SiteAtLevel L m K i,
    (∃! Q, Q ∈ cubePartitionOfSide L m K q ∧ (x : FourTorus L m) ∈ Q) ∧
    (∀ y : SiteAtLevel L m K q, (x : FourTorus L m) ∈ cubeAround y →
      toBareUnits L K (torusSupNorm ((x : FourTorus L m) - (y : FourTorus L m))) < (L : ℝ) ^ q / 2) ∧
    ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K q) X →
      ∀ Q ∈ cubePartitionOfSide L m K q, (x : FourTorus L m) ∈ Q →
        ((x : FourTorus L m) ∈ X ↔ Q ∈ partitionCubesIn (levelDepth K q) X) ∧
        ((x : FourTorus L m) ∈ X →
          {z | toBareUnits L K (torusSupNorm (z - (x : FourTorus L m))) < (L : ℝ) ^ i / 2} ⊆ X)
def RegionsOfNestedPartitions (L m K : ℕ) : Prop :=
  ∀ i q : ℕ, i ≤ q → q ≤ K + 1 → ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K q) X →
    IsPartitionRegion (levelDepth K i) X ∧
      ∀ z : FourTorus L m, z ∉ X → z ∈ complementRegion (levelDepth K q) X
def ComplementRegionIndependentOfScale (L m : ℕ) : Prop :=
  ∀ t t' : ℤ, -(m : ℤ) ≤ t → t ≤ t' → ∀ X : Set (FourTorus L m), IsPartitionRegion t X →
    complementRegion t X = complementRegion t' X
def BlocksAtLevelAreSiteBoxes (L m K i q : ℕ) : Prop :=
  ∀ y : SiteAtLevel L m K q,
    IsSiteBox (levelDepth K i) (sitesIn (blockAtLevel i y) : Set (SiteAtLevel L m K i))
def BareBlockPairsAreSiteBoxes (L m K q : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K q,
    IsSiteBox (levelDepth K 0) (sitesIn (bareBlockPair c) : Set (SiteAtLevel L m K 0)) ∧
    HasSiteCounts (levelDepth K 0) (sitesIn (bareBlockPair c) : Set (SiteAtLevel L m K 0))
      (doubledCounts ((L : ℤ) ^ q) c.axis) ∧
    (∃ (μ : Fin 4) (n : ℤ), IsAxialDisplacement (c.source.toSublattice (levelDepth K 0))
      (c.target.toSublattice (levelDepth K 0)) μ n) ∧
    ∀ z ∈ sitesOfPath (c.source.toSublattice (levelDepth K 0)) (bareAxialPath c),
      (z : FourTorus L m) ∈ bareBlockPair c
def PartialBareBlockFieldLocalCovariant (L m K q : ℕ) : Prop :=
  ∀ (c : BondAtLevel L m K q) (ℬ : Set (BondAtLevel L m K 0)) (U : BondAtLevel L m K 0 → ComplexMatrix2),
    IsDefinedOnBareBlockPair ℬ U c →
      (∀ U' ∈ gaugeFieldsAtLevel L m K 0, (∀ b ∈ bareBondsInBlockPair c, U' b = U b) →
        partialBareBlockField (Averaging.smoothingRadius L) U c =
          blockFieldAtLevel (Averaging.smoothingRadius L) q U' c) ∧
      ∀ (Y : Set (SiteAtLevel L m K 0)) (g : SiteAtLevel L m K 0 → ComplexMatrix2),
        sitesIn (bareBlockPair c) ⊆ Y → (∀ x ∈ Y, g x ∈ compactGaugeGroup) →
          partialBareBlockField (Averaging.smoothingRadius L) (gaugeTransform g U) c =
            g (c.source.toSublattice (levelDepth K 0)) *
              partialBareBlockField (Averaging.smoothingRadius L) U c *
              (g (c.target.toSublattice (levelDepth K 0)))⁻¹
def PartialBlockAverageStepLocalCovariant (L m K i : ℕ) : Prop :=
  ∀ (c : BondAtLevel L m K (i + 1)) (ℬ : Set (BondAtLevel L m K i))
    (W : BondAtLevel L m K i → ComplexMatrix2),
    IsDefinedOnDoubleBlock ℬ W c →
      (∀ W' ∈ gaugeFieldsAtLevel L m K i,
        (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K i)), W' b = W b) →
          partialBlockAverageStep (Averaging.smoothingRadius L) W c =
            blockAverageStep (Averaging.smoothingRadius L) i W' c) ∧
      ∀ (Y : Set (SiteAtLevel L m K i)) (g : SiteAtLevel L m K i → ComplexMatrix2),
        sitesIn (bondDoubleBlock c) ⊆ Y → (∀ x ∈ Y, g x ∈ compactGaugeGroup) →
          partialBlockAverageStep (Averaging.smoothingRadius L) (gaugeTransform g W) c =
            g (c.source.toSublattice (levelDepth K i)) *
              partialBlockAverageStep (Averaging.smoothingRadius L) W c *
              (g (c.target.toSublattice (levelDepth K i)))⁻¹
def RegionBlockAverageEqExtension (L m K q : ℕ) : Prop :=
  ∀ X : Set (FourTorus L m), IsPartitionRegion (levelDepth K q) X →
    ∀ U : BondAtLevel L m K 0 → ComplexMatrix2,
    IsGaugeField compactGaugeGroup (bondsInside X) U →
    ∀ Ũ ∈ gaugeFieldsAtLevel L m K 0,
      (∀ b ∈ (bondsInside X : Set (BondAtLevel L m K 0)), Ũ b = U b) →
      (∀ i : ℕ, i ≤ q → ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K i)),
        regionBlockAverage X U i c = blockFieldAtLevel (Averaging.smoothingRadius L) i Ũ c) ∧
      ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K q)),
        bareBlockPair c ⊆ X ∧
          regionBlockAverage X U q c = partialBareBlockField (Averaging.smoothingRadius L) U c
def SitesOfRegionDifference (L m K i : ℕ) : Prop :=
  ∀ X X' : Set (FourTorus L m), IsPartitionRegion (levelDepth K i) X →
    IsPartitionRegion (levelDepth K i) X' →
    ∀ x : SiteAtLevel L m K i,
      (((x : FourTorus L m) ∈ X ∧ (x : FourTorus L m) ∉ X') ↔
        (x : FourTorus L m) ∈ closure (X \ X')) ∧
      (((x : FourTorus L m) ∈ X ∧ (x : FourTorus L m) ∉ X') ↔
        ∃ Q ∈ cubePartitionOfSide L m K i, (x : FourTorus L m) ∈ Q ∧
          Q ∈ partitionCubesIn (levelDepth K i) X ∧ Q ∉ partitionCubesIn (levelDepth K i) X')
def GeometryAndLocalityOfBlockAverages.Statement : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m → 0 < K →
    SublatticesAndCubesInBareUnits L m K ∧
    (∀ i q : ℕ, i ≤ K → i ≤ q → q ≤ K + 1 → SitesInPartitionCubes L m K i q) ∧
    RegionsOfNestedPartitions L m K ∧
    ComplementRegionIndependentOfScale L m ∧
    (∀ i q : ℕ, i ≤ q → q ≤ K → BlocksAtLevelAreSiteBoxes L m K i q) ∧
    (∀ q : ℕ, q ≤ K → BareBlockPairsAreSiteBoxes L m K q) ∧
    (∀ q : ℕ, q ≤ K → PartialBareBlockFieldLocalCovariant L m K q) ∧
    (∀ i : ℕ, i < K → PartialBlockAverageStepLocalCovariant L m K i) ∧
    (∀ q : ℕ, q ≤ K → RegionBlockAverageEqExtension L m K q) ∧
    ∀ i : ℕ, i ≤ K → SitesOfRegionDifference L m K i
end PeriodicLattice
end
end YangMills.Construction
