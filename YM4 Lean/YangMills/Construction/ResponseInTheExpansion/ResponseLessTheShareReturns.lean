import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def responseSubShareBoundsStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt → T.rt ≤ rt₀ T.toChainParameters → ∃ C₂ : ℝ,
    ∀ K : WeightedResponses.ResponseParameters, C₂ ≤ K.Ka → 0 < K.Kb → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSettings.StepSetup) (A : WeightedResponses.ResponseSetup R),
      A.responseParams = K → WeightedResponses.OnStepParameters T y A → R.IsSymmetricWeight →
      WeightedResponses.HalfDensityBounds R.params (K.Ka * R.nextCoupling ^ (-(1 / 2) : ℝ)) K.η₃
        (WeightedResponses.responseSubShare R.params.coupling A.coldStep A.coeff)
end YangMills.Construction.ResponseInTheExpansion
end
