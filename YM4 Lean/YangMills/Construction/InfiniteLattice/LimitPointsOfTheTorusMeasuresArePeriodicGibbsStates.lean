import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.InfiniteLattice.PeriodicGibbsAndTorusLimitSets
import YangMills.Construction.InfiniteLattice.StatesAndConnectedFunctionsOfTheGrowthCondition
import Mathlib
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace YangMills.Construction.InfiniteLattice
def TorusWeakLimitsArePeriodicGibbs : Prop :=
  ∀ L K : ℕ, Conventions.IsAdmissibleBlockingFactor L → 0 < K → ∀ β : ℝ, 0 < β →
    (∀ ν ∈ GrowthCondition.torusWeakLimits L K β,
      IsGibbs β ν ∧ IsShiftInvariant ν ∧ IsPeriodicMeasure ν) ∧
    GrowthCondition.torusWeakLimits L K β ⊆ periodicGibbsSet L K β
end YangMills.Construction.InfiniteLattice
end
