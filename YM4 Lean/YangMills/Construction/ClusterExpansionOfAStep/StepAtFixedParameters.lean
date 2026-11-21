import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.StepOfAnExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open RenormalizationStepParameters
structure StepSettings.StepSetup.OnParameters (R : StepSettings.StepSetup) (T : ParameterAssignment) (y : ℝ) : Prop where
  params_eq : R.params = T.stepParameters y
  anchorRadius_eq : R.anchorRadius = T.ρA
  barrierFn_eq : R.barrierFn = T.cutoff
  le_coupling : y ≤ R.coupling
  isStep : R.IsStep
end YangMills.Construction
end
