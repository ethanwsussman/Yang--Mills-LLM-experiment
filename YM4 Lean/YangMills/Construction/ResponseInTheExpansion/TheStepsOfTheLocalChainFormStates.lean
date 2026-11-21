import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def localChainStepsWellPosedAt : Prop :=
  ∀ (T : WeightedResponses.StageTower (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y)) (β : ℝ) (k N : ℕ) (nn x₀ : ℝ),
    IsLocalChainAbove Tb y T β k N nn x₀ →
    ∀ s ≤ k + 2 * localChainDepth (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y) β k,
      (T.stage s).depth = s ∧ (T.stage s).coupling = flowCouplings (RenormalizationStepParameters.ParameterAssignment.stepParameters Tb y) β s ∧
      |(T.stage s).nextCoupling - (T.stage s).coupling| ≤ 2 * Tb.B ∧ (T.stage s).toStepSetup.IsWellPosed
def localChainStepsWellPosedStatement : Prop := HoldsOnParameterFamilies localChainStepsWellPosedAt
end YangMills.Construction.ResponseInTheExpansion
end
