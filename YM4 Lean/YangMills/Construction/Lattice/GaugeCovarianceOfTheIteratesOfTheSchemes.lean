import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnPartOfTheBareLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def IteratedAverageGaugeCovariance : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ K m : ℕ, 0 < K → 0 < m →
    ∀ s : AveragingScheme, ∀ j : ℕ, j ≤ K →
    ∀ U ∈ gaugeFieldsAtLevel L m K 0, ∀ g : SiteAtLevel L m K 0 → Matrices.ComplexMatrix2,
      IsGaugeMap compactGaugeGroup g → ∀ c : BondAtLevel L m K j,
        IsBareIterateDefined s U j c →
          IsBareIterateDefined s (gaugeTransform g U) j c ∧
            iteratedAverage s j (gaugeTransform g U) c =
              gaugeTransform (fun y => g (finestBaseSite s K j y)) (iteratedAverage s j U) c
end YangMills.Construction.PeriodicLattice
