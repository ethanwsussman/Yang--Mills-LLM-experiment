import YangMills.Construction.SystemsWithFiveBounds.ConditionsOfALimitAtConstantsForm
import YangMills.Construction.SystemsWithFiveBounds.StatesOfTheWindowForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SystemsWithFiveBounds
def BaseAndLawConditionsAtExistentialConstants : Prop :=
  ∀ (M : ℝ) (N : BoundConstants),
    BaseConditionsAt M N (existentialConstants M N) ∧ LawConditionsAt M N (existentialConstants M N)
end YangMills.Construction.SystemsWithFiveBounds
end
