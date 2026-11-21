import YangMills.Construction.Averaging.SmoothingRadius
import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.Lattice.CaseSetsOfTheAveragingMap
import Mathlib
noncomputable section
namespace YangMills.Construction
namespace PeriodicLattice
def BlockAverageIsBorelMap : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ k : ℕ, k < (s.K : ℕ) →
    BlockAverageBorel s.L s.m s.K (Averaging.smoothingRadius s.L) k
end PeriodicLattice
end YangMills.Construction
end
