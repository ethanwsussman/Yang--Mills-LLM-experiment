import YangMills.Construction.ClusterExpansionOfAStep.FamiliesAtConstantCurvature
import YangMills.Construction.ClusterExpansionOfAStep.StepAtFixedParameters
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open TorusLumps StepSettings RenormalizationStepParameters BlockAverages
def remaindersInvariantUnderIsometries : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ y : ℝ, T.floorMin ≤ y → ∀ (R : StepSetup) (A : ResponseSetup R),
    R.OnParameters T y → A.IsAdmissible →
    SumInvariantUnderIsometries R.params A.totalRemainder ∧ SumInvariantUnderIsometries R.params A.siteRemainder
end YangMills.Construction.WeightedResponses
end
