import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.AveragesOnPartOfTheBareLattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicLattice
def TrivialFieldAverages.Statement : Prop :=
  ∀ L : ℕ, YangMills.Construction.Conventions.IsAdmissibleBlockingFactor L →
    ∀ m K : ℕ, 0 < m → ∀ s : AveragingScheme,
    (∀ j : ℕ, j ≤ K → ∀ c : BondAtLevel L m K j,
      IsBareIterateDefined s trivialGaugeField j c ∧
        iteratedAverage s j trivialGaugeField c = 1) ∧
    ∀ j : ℕ, j < K → ∀ (y : SiteAtLevel L m K (j + 1)) (x : SiteAtLevel L m K j),
      x ∈ sitesInBlock (levelDepth K j) y →
        IsContourHolonomyDefined s (iteratedAverage s j trivialGaugeField) y x ∧
          contourHolonomy s (iteratedAverage s j trivialGaugeField) y x = 1
end YangMills.Construction.PeriodicLattice
