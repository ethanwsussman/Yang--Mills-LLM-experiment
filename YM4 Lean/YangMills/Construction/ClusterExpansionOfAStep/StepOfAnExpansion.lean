import YangMills.Construction.ClusterExpansionOfAStep.SettingsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
def StepSetup.IsStep (R : StepSetup) : Prop :=
  R.HasExpansions ∧ R.coupling ≤ 1.01 * R.nextCoupling ∧ R.range ≤ R.nextRange + 1
end StepSettings
end YangMills.Construction
end
