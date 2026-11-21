import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CaseSetsOfTheAveragingMap
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockAverageContinuousOnEachCaseSet : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ k : ℕ, k < (s.K : ℕ) →
    ∀ c : BondAtLevel s.L s.m s.K (k + 1), c.IsPositivelyOriented →
      BlockAverageContinuousOnCaseSets (Averaging.smoothingRadius s.L) k c
end PeriodicLattice
end YangMills.Construction
end
