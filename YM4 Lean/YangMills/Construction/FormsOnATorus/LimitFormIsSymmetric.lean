import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def limitFormSymmetricStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (c C : ℝ) (k : ℕ) (Q : IntBond → IntBond → ℝ),
    IsLimitForm T.coupling T.coercivity c C T.side k Q → ∀ b b', Q b b' = Q b' b
end YangMills.Construction.LimitForms
end
