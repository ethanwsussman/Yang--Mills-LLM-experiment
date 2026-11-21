import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.SumOfAClassAtAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open RenormalizationStepParameters
def ParameterChoiceMeetsClassSum : Prop :=
  ∀ (T : ParameterAssignment), T.Admissible → ∀ CE c y : ℝ, 0 ≤ CE → T.floorMin ≤ y →
    (∀ x, y ≤ x → T.FloorConditions (2 ^ 18 * CE + 2 ^ 17) c x) →
    ClassSumHypotheses (T.stepParameters y) T.cE CE
end YangMills.Construction.ClusterExpansionOfAStep
end
