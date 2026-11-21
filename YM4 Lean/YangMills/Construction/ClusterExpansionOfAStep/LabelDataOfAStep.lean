import YangMills.Construction.ClusterExpansionOfAStep.ActionOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
def CoarseLabelsStandard : Prop :=
  ∀ R : StepSettings.StepSetup, 2 ≤ R.params.side → CoarseLabelFacts R
end ClusterExpansionOfAStep
end YangMills.Construction
end
