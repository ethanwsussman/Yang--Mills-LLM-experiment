import YangMills.Construction.ResponseInTheExpansion.ConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
open StepSettings
def StepDecayBoundsHold : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsWellPosed → ∀ hL, StepDecayBounds A hL
end YangMills.Construction.WeightedResponses
end
