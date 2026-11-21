import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TorusLimitsSubsetPeriodicGibbs : Prop :=
  ∀ s : Conventions.StandingParameters, ∀ β : ℝ, 0 < β →
    torusLimitSet s.L s.K β ⊆ periodicGibbsSet s.L s.K β
end YangMills.Construction.InfiniteLattice
