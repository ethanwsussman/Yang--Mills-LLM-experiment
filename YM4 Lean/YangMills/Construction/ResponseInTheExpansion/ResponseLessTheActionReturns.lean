import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
def totalResponseSubActionStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt → T.rt ≤ rt₀ T.toChainParameters → ∃ C₃ : ℝ,
    ∀ K : WeightedResponses.ResponseParameters, C₃ ≤ K.Kb → ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSettings.StepSetup) (A : WeightedResponses.ResponseSetup R),
      A.responseParams = K → WeightedResponses.OnStepParameters T y A → R.IsSymmetricWeight →
      ∃ G : TorusLumps.LocalDensity, WeightedResponses.HalfDensityBounds R.params (K.Kb * R.nextCoupling⁻¹) K.η₃ G ∧
        WeightedResponses.IsTotalRemainder R.params A.coldStep A.coeff G
end YangMills.Construction.ResponseInTheExpansion
end
