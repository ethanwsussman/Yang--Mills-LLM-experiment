import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfASetting
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields StepSettings RenormalizationStepParameters
def LogJacobianBound : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ C y₀ : ℝ, 0 < C ∧ ∀ (y : ℝ) (R : StepSetup),
    R.params = T.stepParameters y → R.anchorRadius = T.ρA →
    y₀ ≤ R.coupling → ∀ (n : ℕ) [NeZero n] (s : ChartSetting R n) (Y : TorusSite n) (η : FreeCoords s.free),
      s.InBalls η → |s.logJacobianAt Y η| ≤ C * Real.log R.coupling
end YangMills.Construction.ClusterExpansionOfAStep
end
