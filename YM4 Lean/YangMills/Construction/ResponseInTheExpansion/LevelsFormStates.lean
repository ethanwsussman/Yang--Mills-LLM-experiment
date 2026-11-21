import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings
open YangMills.Construction.WeightedResponses YangMills.Construction.ClusterExpansionOfAStep
def StagesAreWellPosed : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ (K : ResponseParameters) (β : ℝ)
    (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (T.stepParameters y)),
    IsInitialStage T y β z₀ → ∀ s : ℕ, StagesOnFlowUpTo T K y β hL z₀ s → ∀ t ≤ s,
      (flowStages T y β hL z₀ t).1.toStepSetup.IsWellPosed
end YangMills.Construction.ResponseInTheExpansion
end
