import YangMills.Construction.ClusterExpansionOfAStep.ColdRenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.ColdConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses YangMills.Construction.RenormalizationStepParameters YangMills.Construction.StepSettings YangMills.Construction.TorusLumps YangMills.Construction.BlockAverages
def coldResponseUniqueCoefficient : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ T : ParameterAssignment, T.coupling = a → L₀ ≤ T.side → T.Admissible → T.ColdStepHolds → T.HoldsFrom ColdRegimeEstimatesAt →
    T.rt ≤ rt₀ T.toChainParameters → ∃ C₁ C₂ C₃ : ℝ,
    ∀ K : ResponseParameters, C₁ ≤ K.Kc → C₂ ≤ K.Ka → C₃ ≤ K.Kb → ∃ C y₀ : ℝ, 0 ≤ C ∧ ∀ y : ℝ, y₀ ≤ y →
      ∀ (R : StepSetup) (A : ResponseSetup R), A.responseParams = K → OnStepParameters T y A → R.IsSymmetricWeight →
        ∃ c' : ℝ, |c' - A.coeff| ≤ C * R.coupling ^ (-(3 / 2) : ℝ) ∧
          (∃ Ra Rb : LocalDensity, ColdResponseBounds R.params K (R.depth + 1) R.nextCoupling c' A.coldStep Ra Rb) ∧
          ∀ c'' : ℝ, (∃ Ra Rb : LocalDensity,
              ColdResponseBounds R.params K (R.depth + 1) R.nextCoupling c'' A.coldStep Ra Rb) →
            c'' = c'
end YangMills.Construction.ResponseInTheExpansion
end
