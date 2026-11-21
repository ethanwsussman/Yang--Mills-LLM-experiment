import YangMills.Construction.ResponseInTheExpansion.ConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses StepSettings
def ResponseShapeStatement : Prop :=
  HoldsAtEveryStep fun _ R A => R.IsWellPosed → ∀ hL, StepShapeBounds A hL
end YangMills.Construction.ResponseInTheExpansion
end
