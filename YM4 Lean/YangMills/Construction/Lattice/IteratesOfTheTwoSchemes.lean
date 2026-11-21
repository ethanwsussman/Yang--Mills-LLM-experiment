import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnPartOfTheBareLattice
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def IteratedAverageGaugeLocality : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ m K : ℕ, 0 < m → 0 < K →
    ∀ s : AveragingScheme, ∀ j : ℕ, j ≤ K →
    (∀ y : SiteAtLevel L m K j,
      finestBaseSite .cornered K j y ∈ sitesIn (refinedBlock j y) ∧
      ∀ z ∈ (sitesIn (refinedBlock j y) : Set (SiteAtLevel L m K 0)),
        ∃ d, IsChartOffset (finestBaseSite .cornered K j y) z d ∧ ∀ μ, 0 ≤ d μ) ∧
    (∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup g →
        (gaugeTransform g U ∈ iteratedAverageDomain s j ↔ U ∈ iteratedAverageDomain s j)) ∧
    (∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup g → U ∈ iteratedAverageDomain s j →
        iteratedAverage s j (gaugeTransform g U) =
          gaugeTransform (fun y => g (finestBaseSite s K j y)) (iteratedAverage s j U)) ∧
    (∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup g → ∀ c : BondAtLevel L m K j,
        (IsBareIterateDefined s (gaugeTransform g U) j c ↔
          IsBareIterateDefined s U j c)) ∧
    (∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup g → ∀ c : BondAtLevel L m K j,
        IsBareIterateDefined s U j c →
          iteratedAverage s j (gaugeTransform g U) c =
            gaugeTransform (fun y => g (finestBaseSite s K j y)) (iteratedAverage s j U) c) ∧
    ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ V ∈ gaugeFieldsAtLevel L m K 0,
      ∀ c : BondAtLevel L m K j,
        (∀ b ∈ bondsInside (refinedBlock j c.source ∪ refinedBlock j c.target), U b = V b) →
          (IsBareIterateDefined s U j c ↔ IsBareIterateDefined s V j c) ∧
            (IsBareIterateDefined s U j c →
              iteratedAverage s j U c = iteratedAverage s j V c)
end PeriodicLattice
end YangMills.Construction
