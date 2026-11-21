import YangMills.Construction.ResponseInTheExpansion.ConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open YangMills.Construction.StepSettings
def StepSizeBoundsOfCold : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsWellPosed → ∀ hL, coldStepSizeBound A → StepSizeBounds A hL
end YangMills.Construction.WeightedResponses
end
