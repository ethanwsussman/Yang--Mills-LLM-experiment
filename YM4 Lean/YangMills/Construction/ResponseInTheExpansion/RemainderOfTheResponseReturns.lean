import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
def responseRemainderBoundsStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt → T.rt ≤ rt₀ T.toChainParameters → ∃ C₁ : ℝ,
    ∀ K : WeightedResponses.ResponseParameters, C₁ ≤ K.Kc → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSettings.StepSetup) (A : WeightedResponses.ResponseSetup R),
      A.responseParams = K → WeightedResponses.OnStepParameters T y A → R.IsSymmetricWeight →
        WeightedResponses.RemainderBounds R.params K (R.depth + 1) A.coldStep
end ResponseInTheExpansion
end YangMills.Construction
end
