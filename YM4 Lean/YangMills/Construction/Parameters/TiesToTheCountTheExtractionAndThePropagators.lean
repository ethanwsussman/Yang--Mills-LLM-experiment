import YangMills.Construction.Parameters.FamiliesOfTheDeterminedAndNamedNumbers
import YangMills.Construction.PolymerActivities.DomainCountingRate
import YangMills.Construction.SeparatedSequences.NumbersOfTheSettingOfThePropagators
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ParameterChoice
structure PropagatorCountingTies (N : ExternalConstants) : Prop where
  propagatorFloor_eq : ∀ L : ℕ, BlockingFactorAdmissible L →
    N.propagatorFloor L = (SeparatedSequences.propagatorScaleFloor L : ℝ)
  Cδ_pos : 0 < N.Cδ
  countingRate_lt_κAnalytic : PolymerActivities.DomainCounting.countingRate < N.κAnalytic
end YangMills.Construction.ParameterChoice
end
