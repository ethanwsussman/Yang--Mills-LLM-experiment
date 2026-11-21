import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import YangMills.Construction.TotalDensitiesGiveASystem.FirstExitPathDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TotalDensitiesGiveASystem
def ResponseParametersToAdmissibleParameters : Prop :=
  ∀ P : RenormalizationStepParameters.ParameterAssignment → ℝ → Prop, ResponseInTheExpansion.HoldsOnParameterFamilies P →
    TotalDensities.HoldsAtAdmissibleParameters P
end YangMills.Construction.TotalDensitiesGiveASystem
end
