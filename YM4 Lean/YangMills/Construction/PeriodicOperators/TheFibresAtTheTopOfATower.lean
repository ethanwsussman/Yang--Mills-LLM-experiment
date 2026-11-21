import YangMills.Construction.Conventions.StandingParameters
import YangMills.Construction.PeriodicOperators.PeriodicIndexSetsOperatorsAndSymbols
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicOperators.TopFibreDimension
def Claim : Prop :=
  ∀ L : ℕ, Conventions.IsAdmissibleBlockingFactor L → ∀ k : ℕ, 1 ≤ k →
    Module.finrank ℂ ((colourEdges L k k).UnitQuot → ℂ) = 12 ∧
      Module.finrank ℂ ((colourVertices L k k).UnitQuot → ℂ) = 3
end YangMills.Construction.PeriodicOperators.TopFibreDimension
end
