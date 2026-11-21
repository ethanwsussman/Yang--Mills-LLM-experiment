import YangMills.Construction.ColdStepAtMirrorFrames.ParametersOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def EventuallyInParametersCombines : Prop :=
  (∀ P Q : StepParameters → Prop, EventuallyInParameters P → EventuallyInParameters Q →
    EventuallyInParameters fun T => P T ∧ Q T) ∧
  ∀ P Q : StepParameters → Prop, (∀ T, T.IsOrdered → P T → Q T) →
    EventuallyInParameters P → EventuallyInParameters Q
end YangMills.Construction.ColdStepAtMirrorFrames
end
