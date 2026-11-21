import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.StepFloors
open YangMills.Construction.RenormalizationStepParameters
def EventuallyFloorConditions : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ C c : ℝ, 0 < C → 0 < c → ∃ y : ℝ, ∀ x : ℝ, y ≤ x →
    T.FloorConditions C c x
end YangMills.Construction.StepFloors
end
