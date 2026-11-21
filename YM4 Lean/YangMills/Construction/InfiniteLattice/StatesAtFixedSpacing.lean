import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets

namespace YangMills.Construction.InfiniteLattice

/-- Exactly the fixed-spacing existence fact used by the two limit constructions. -/
def TorusLimitSetsNonempty : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K →
    ∀ β : ℝ, 0 < β → (torusLimitSet L K β).Nonempty

end YangMills.Construction.InfiniteLattice
