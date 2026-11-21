import YangMills.Construction.ClusterExpansionOfAStep.FlowOfTheExpansion
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ClusterExpansionOfAStep.TheExpansionReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
def FlowStaysAbove (ℓ : TorusLumps.StepParameters) (β : ℝ) (j : ℕ) : Prop :=
  ∀ k < j, ℓ.y₁ ≤ (TorusLumps.couplingFlow ℓ β k).1
def HasLinearDescent (ℓ : TorusLumps.StepParameters) (lam c₅ : ℝ) : Prop :=
  ∀ β : ℝ, ℓ.y₁ ≤ β → ∀ j : ℕ, FlowStaysAbove ℓ β j → ∀ i : ℕ, i ≤ j →
    lam * ((j : ℝ) - i) - c₅ ≤ (TorusLumps.couplingFlow ℓ β i).1 - (TorusLumps.couplingFlow ℓ β j).1
def FlowDescendsLinearly : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∃ lam c₅ : ℝ, 0 < lam ∧ ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible →
      T.rt ≤ rt₀ T.toChainParameters →
      ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
        (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) →
        HasLinearDescent (T.stepParameters y) lam c₅
end YangMills.Construction.WeightedResponses
end
