import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages LumpContours ColdStepAtMirrorFrames
namespace ResponseInTheExpansion
open RenormalizationStepParameters StepSettings WeightedResponses ClusterExpansionOfAStep
def flowStagesAreChainStatement : Prop :=
  HoldsOnParameterFamilies fun Tb y => ∀ K : ResponseParameters, K.Admissible (Tb.stepParameters y) → ∀ (β : ℝ)
    (hL : ∀ c : ChainStage (Tb.stepParameters y), CoarseLabelFacts c.toStepSetup)
    (z₀ : StageWithResponse (Tb.stepParameters y)) (s : ℕ), IsInitialStage Tb y β z₀ →
      StagesOnFlowUpTo Tb K y β hL z₀ s →
      IsChainResponseCoeff (Tb.stepParameters y) K β s fun j => (flowStages Tb y β hL z₀ j).2.coeff
end ResponseInTheExpansion
end YangMills.Construction
end
