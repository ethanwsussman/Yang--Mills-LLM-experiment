import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.HoleBesideASecondHole.TheInequalityOfAHoleOnTori
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RenormalizationStepParameters
open HoleBounds HoleOnTori
def HoleSavingAtFixedParameters : Prop :=
  ∀ T : ParameterAssignment, T.Admissible →
    HoleSavingWorkingBounds T.grid T.coupling T.κ T.threshold T.cE T.baseDepth ∧
      ∀ y : ℝ, HoleSavingBounds (T.stepParameters y) T.cE
end YangMills.Construction.RenormalizationStepParameters
end
