import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.GaugeFixingFactor
import YangMills.Construction.Lattice.RenormalizationTransformation
import YangMills.Construction.Lattice.SetsOfBondsOfASequenceOfRegions
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
noncomputable section
namespace YangMills.Construction.PeriodicLattice
variable {L m : ℕ} {k : ℤ}
def sitePointImage (σ : FourTorus L m ≃ FourTorus L m) (P : Set (Site L m k)) :
    Set (Site L m k) :=
  {x | ∃ y ∈ P, (x : FourTorus L m) = σ y}
def GaugeFixingCovarianceStatement : Prop :=
  ∀ (L m : ℕ) (i : ℤ), Conventions.IsAdmissibleBlockingFactor L → 0 < m → -(m : ℤ) ≤ i →
    ∀ σ ∈ latticeIsometries L m i,
      (∀ j : ℤ, i ≤ j → ∀ (B : Set (Bond L m j)) (U : Bond L m j → Matrices.ComplexMatrix2)
          (u : Site L m j → Matrices.ComplexMatrix2),
        IsReversalClosed B → IsGaugeField compactGaugeGroup B U → IsGaugeMap compactGaugeGroup u →
        ∀ e ∈ bondImage σ '' B,
          transportGaugeField σ (gaugeTransform u U) e =
            gaugeTransform (transportSiteFunction σ u) (transportGaugeField σ U) e) ∧
      (∀ (K n : ℕ) (Ω : ℕ → Set (FourTorus L m)), n ≤ K → IsDeterminingChain K n Ω →
        (∀ q ≤ n, ∃ c : ℤ, i ≤ c ∧ c ≤ levelDepth K q ∧ IsPartitionRegion c (Ω q)) →
        ∀ (V : ∀ q : ℕ, BondAtLevel L m K q → Matrices.ComplexMatrix2)
          (v : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2),
          IsDeterminingDatum K n Ω V → IsGaugeMap compactGaugeGroup v →
          ∀ q ∈ bondSetImage σ (determiningBondSet K n Ω),
            datumImage σ (gaugeTransformDatum v V) q.1 q.2 =
              gaugeTransformDatum (transportSiteFunction σ v) (datumImage σ V) q.1 q.2) ∧
      ∀ K n : ℕ, n < K → i ≤ levelDepth K (n + 1) →
        (∀ (A₀ : ℝ) (r₀ : ℕ) (x : ℕ → ℝ) (P : Set (SiteAtLevel L m K (n + 1)))
            (V : BondAtLevel L m K n → Matrices.ComplexMatrix2),
          V ∈ gaugeFieldsAtLevel L m K n →
          (HasOffCenterContours K n (sitePointImage σ P) (transportGaugeField σ V) ↔
              HasOffCenterContours K n P V) ∧
            axialGaugeFactor A₀ r₀ x K n (transportGaugeField σ V) (sitePointImage σ P) =
              axialGaugeFactor A₀ r₀ x K n V P ∧
            (HasOffCenterContours K n P V →
              axialGaugeFunction K n (sitePointImage σ P) (transportGaugeField σ V) =
                axialGaugeFunction K n P V)) ∧
        (∀ (P : Set (SiteAtLevel L m K (n + 1))) (V : BondAtLevel L m K n → Matrices.ComplexMatrix2),
          IsBlockAxialGauge K n (sitePointImage σ P) (transportGaugeField σ V) ↔
            IsBlockAxialGauge K n P V) ∧
        ∀ ν : Measure (BondAtLevel L m K n → Matrices.ComplexMatrix2), IsFiniteGaugeMeasure n ν →
          rgMap (K := K) n (transportMeasure σ ν) =
            transportMeasure σ (rgMap n ν)
end YangMills.Construction.PeriodicLattice
