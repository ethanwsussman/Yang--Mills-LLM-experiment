import YangMills.Construction.SystemsWithFiveBounds.ConditionsOfALimitAtConstantsForm
import YangMills.Construction.SystemsWithFiveBounds.StatesOfTheWindowForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def RotationConditionsAtExistentialConstants : Prop :=
  ∀ (M : ℝ) (N : BoundConstants), (existentialConstants M N).SideConditions →
    RotationConditionsAt M N (existentialConstants M N)
end YangMills.Construction.SystemsWithFiveBounds
end
