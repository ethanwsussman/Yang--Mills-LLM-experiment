import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.LawOnABoxOfTheFlow.LimitFormDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LimitForms
def limitFormSecondMomentStatement : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (c C : ℝ) (k : ℕ) (Q : IntBond → IntBond → ℝ), 0 < c →
    IsLimitForm T.coupling T.coercivity c C T.side k Q → ∀ i l : Fin 4, i ≠ l →
      HasSum (fun z : Fin 4 → ℤ => Q (0, i) (z, i) * (z l : ℝ) ^ 2) (-2)
end YangMills.Construction.LimitForms
end
