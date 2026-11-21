import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CaseSetsOfTheAveragingMap
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockAverageSmallSetAndMeasurable : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ k : ℕ, k < (s.K : ℕ) →
    (∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented →
      BlockAverageAnalyticNearOne (Averaging.smoothingRadius s.L) k c ∧
        CaseSetsMeasurable (Averaging.smoothingRadius s.L) k c ∧
        BlockAverageContinuousOnCaseSets (Averaging.smoothingRadius s.L) k c) ∧
      BlockAverageBorel s.L s.m s.K (Averaging.smoothingRadius s.L) k
end PeriodicLattice
end YangMills.Construction
end
