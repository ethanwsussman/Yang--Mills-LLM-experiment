import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import YangMills.Construction.ClusterExpansionOfAStep.TheFlowIsTheLawOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusLumps StepReturn
def FlowWhereExpansionReturns : Prop :=
  ∃ C₀ : ℝ, ∀ ℓ : StepParameters, ℓ.Admissible → C₀ ≤ ℓ.derivBound → ExpansionReturnsAt ℓ →
    (∀ β : ℝ, FlowIsChainLawAt ℓ β) ∧
      ∀ β : ℝ, ℓ.y₁ ≤ β → FlowHasExpansionAt ℓ β ∧ FlowReadOffAt ℓ β ∧ FlowUniqueAt ℓ β
end YangMills.Construction.ClusterExpansionOfAStep
end
