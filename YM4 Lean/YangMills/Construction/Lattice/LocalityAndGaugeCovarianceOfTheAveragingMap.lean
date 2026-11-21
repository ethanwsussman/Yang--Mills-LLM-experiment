import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOfAConfigurationOnARegion
import YangMills.Construction.Lattice.BondwiseAverage
import YangMills.Construction.Lattice.CubePartitionsAndRegions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
variable {L m K : ℕ}
def gaugeOrbitOf {j : ℤ} (U : Bond L m j → Matrices.ComplexMatrix2) :
    Set (Bond L m j → Matrices.ComplexMatrix2) :=
  {V | ∃ u : Site L m j → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup u ∧ V = gaugeTransform u U}
def MeanContourCovariantAt {k : ℕ} (U : BondAtLevel L m K k → Matrices.ComplexMatrix2)
    (u : SiteAtLevel L m K k → Matrices.ComplexMatrix2) (y : SiteAtLevel L m K (k + 1)) : Prop :=
  ∀ x ∈ sitesInBlock (levelDepth K k) y, HasContourMean U y x →
    HasContourMean (gaugeTransform u U) y x ∧
      meanContourHolonomy (gaugeTransform u U) y x =
        u (y.toSublattice (levelDepth K k)) * meanContourHolonomy U y x * (u x)⁻¹
def BlockAverageGaugeCovariant (L m K k : ℕ) : Prop :=
  ∀ U ∈ gaugeFieldsAtLevel L m K k, ∀ u : SiteAtLevel L m K k → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u →
      (∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
        blockAverageCase (Averaging.smoothingRadius L) (gaugeTransform u U) c =
          blockAverageCase (Averaging.smoothingRadius L) U c) ∧
      (∀ y : SiteAtLevel L m K (k + 1), MeanContourCovariantAt U u y) ∧
      (blockAverage (Averaging.smoothingRadius L) (gaugeTransform u U) :
          BondAtLevel L m K (k + 1) → Matrices.ComplexMatrix2) =
        gaugeTransform (restrictGaugeMap (k + 1) u) (blockAverage (Averaging.smoothingRadius L) U)
def PartialBlockAverageGaugeCovariant (L m K k : ℕ) : Prop :=
  ∀ a : ℤ, -(m : ℤ) ≤ a → a ≤ levelDepth K (k + 1) → ∀ X : Set (FourTorus L m), IsPartitionRegion a X →
    ∀ U : BondAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside X) U →
    ∀ u : SiteAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup u →
      (∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))), c.IsPositivelyOriented →
        blockAverageCase (Averaging.smoothingRadius L) (extendByOne (bondsInside X) (gaugeTransform u U)) c =
          blockAverageCase (Averaging.smoothingRadius L) (extendByOne (bondsInside X) U) c) ∧
      (∀ y : SiteAtLevel L m K (k + 1),
        (bondsInside (unitBlock y) : Set (BondAtLevel L m K k)) ⊆ bondsInside X →
          MeanContourCovariantAt U u y) ∧
      ∀ c ∈ (bondsInside X : Set (BondAtLevel L m K (k + 1))),
        partialBlockAverage (K := K) (j := k) (Averaging.smoothingRadius L) 1 (bondsInside X)
            (gaugeTransform u U) c =
          gaugeTransform (restrictGaugeMap (k + 1) u)
            (partialBlockAverage (K := K) (j := k) (Averaging.smoothingRadius L) 1 (bondsInside X) U) c
def BlockAverageLocalToDoubleBlock (L m K k : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
    ∀ U ∈ gaugeFieldsAtLevel L m K k, ∀ U' ∈ gaugeFieldsAtLevel L m K k,
      (∀ b ∈ (bondsInDoubleBlock c : Set (BondAtLevel L m K k)), U b = U' b) →
        blockAverage (Averaging.smoothingRadius L) U c = blockAverage (Averaging.smoothingRadius L) U' c ∧
          blockAverageCase (Averaging.smoothingRadius L) U c =
            blockAverageCase (Averaging.smoothingRadius L) U' c
def BlockAverageIterLocal (L m K j n : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (j + n), ∀ W ∈ gaugeFieldsAtLevel L m K j,
    ∀ W' ∈ gaugeFieldsAtLevel L m K j,
      (∀ b ∈ (bondsInside (refinedBlock n c.source ∪ refinedBlock n c.target) :
          Set (BondAtLevel L m K j)), W b = W' b) →
        blockAverageIter (Averaging.smoothingRadius L) j n W c =
          blockAverageIter (Averaging.smoothingRadius L) j n W' c
def BlockFieldGaugeCovariant (L m K n : ℕ) : Prop :=
  ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
    IsGaugeMap compactGaugeGroup u →
      (blockFieldAtLevel (Averaging.smoothingRadius L) n (gaugeTransform u U) :
          BondAtLevel L m K n → Matrices.ComplexMatrix2) =
        gaugeTransform (restrictGaugeMap n u) (blockFieldAtLevel (Averaging.smoothingRadius L) n U)
def RegionBlockFieldGaugeCovariant (L m K n : ℕ) : Prop :=
  ∀ a : ℤ, -(m : ℤ) ≤ a → a ≤ levelDepth K n → ∀ Ω : Set (FourTorus L m), IsPartitionRegion a Ω →
    ∀ U : BondAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeField compactGaugeGroup (bondsInside Ω) U →
    ∀ u : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup u →
      ∀ c ∈ (bondsInside Ω : Set (BondAtLevel L m K n)),
        regionBlockField n Ω (gaugeTransform u U) c =
          gaugeTransform (restrictGaugeMap n u) (regionBlockField n Ω U) c
def BlockFieldMapsOrbitsToOrbits (L m K n : ℕ) : Prop :=
  ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∃ V ∈ gaugeFieldsAtLevel L m K n,
    (blockFieldAtLevel (Averaging.smoothingRadius L) n :
        (BondAtLevel L m K 0 → Matrices.ComplexMatrix2) → BondAtLevel L m K n → Matrices.ComplexMatrix2) ''
      gaugeOrbitOf U ⊆ gaugeOrbitOf V
def ComplexBlockAverageGaugeCovariant (L m K k : ℕ) : Prop :=
  ∀ c : BondAtLevel L m K (k + 1), c.IsPositivelyOriented →
    ∀ U ∈ (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)),
    ∀ u : SiteAtLevel L m K k → Matrices.ComplexMatrix2, IsGaugeMap compactGaugeGroup u →
      gaugeTransform u U ∈
          (complexAveragingDomainNearOne c : Set (BondAtLevel L m K k → Matrices.ComplexMatrix2)) ∧
      (∀ y ∈ ({c.source, c.target} : Set (SiteAtLevel L m K (k + 1))),
        ∀ x ∈ sitesInBlock (levelDepth K k) y,
          complexMeanContourHolonomy (gaugeTransform u U) y x =
            u (y.toSublattice (levelDepth K k)) * complexMeanContourHolonomy U y x * (u x)⁻¹) ∧
      complexBlockAverage (gaugeTransform u U) c =
        u (c.source.toSublattice (levelDepth K k)) * complexBlockAverage U c *
          (u (c.target.toSublattice (levelDepth K k)))⁻¹
def BlockAverageLocalityAndCovariance : Prop :=
  ∀ L m K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < m →
    (∀ k : ℕ, k < K →
      BlockAverageGaugeCovariant L m K k ∧ PartialBlockAverageGaugeCovariant L m K k ∧
        BlockAverageLocalToDoubleBlock L m K k ∧ ComplexBlockAverageGaugeCovariant L m K k) ∧
    (∀ j n : ℕ, j + n ≤ K → BlockAverageIterLocal L m K j n) ∧
    ∀ n : ℕ, n ≤ K →
      BlockFieldGaugeCovariant L m K n ∧ RegionBlockFieldGaugeCovariant L m K n ∧
        BlockFieldMapsOrbitsToOrbits L m K n
end PeriodicLattice
end YangMills.Construction
