import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ResponseInTheExpansion
open WeightedResponses RenormalizationStepParameters StepSettings TorusLumps
def responseCurvatureCoeffStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds →
    T.HoldsFrom ColdRegimeEstimatesAt → T.rt ≤ rt₀ T.toChainParameters →
    ∃ C₂ : ℝ, ∀ K : ResponseParameters, C₂ ≤ K.Ka → 0 < K.Kb →
    ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y → ∀ (S : StepSetup) (A : ResponseSetup S),
      A.responseParams = K → OnStepParameters T y A → S.IsSymmetricWeight →
      ∃ b : ℝ, |b| ≤ C * S.coupling ^ (-(3 / 2) : ℝ) ∧
        HasCurvatureForm (responseSubShare S.params.coupling A.coldStep A.coeff) b ∧
        ∀ G : LocalDensity, HalfDensityBounds S.params (K.Kb * S.nextCoupling⁻¹) K.η₃ G →
          IsTotalRemainder S.params A.coldStep A.coeff G → HasCurvatureForm G b
end ResponseInTheExpansion
end YangMills.Construction
end
