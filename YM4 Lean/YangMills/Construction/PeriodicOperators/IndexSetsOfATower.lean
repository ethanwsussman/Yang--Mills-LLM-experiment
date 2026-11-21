import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators
namespace TowerIndexSets
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k j : ℕ, j ≤ k →
    IsPeriodic (colourVertices L k j) ∧
    IsPeriodic (colourEdges L k j) ∧
    IsPeriodic (colourFaces L k j)
end TowerIndexSets
end YangMills.Construction.PeriodicOperators
end
