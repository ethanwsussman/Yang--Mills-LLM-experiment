import YangMills.Construction.Parameters.BoundParameters
import YangMills.Construction.PolymerActivities.FlowOfTheConstruction
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ParameterChoice
namespace PeriodicLattice.CubesOfStep
structure FixedParameterFlow where
  derived : DerivedConstants
  params : FullChoice
  isAdmissible : Conventions.IsAdmissibleBlockingFactor params.L
  K : ℕ+
  m : ℕ+
  m' : ℕ
  M_eq_pow : params.M = params.L ^ m'
  two_le_r : ExponentLowerBound (params.r : ℝ)
  β : ℝ
  activityDomain : ActivityDomainKind
  remainders : FlowRemainders
    params.toChoiceUpToDegreeConstants K
end PeriodicLattice.CubesOfStep
end YangMills.Construction
end
