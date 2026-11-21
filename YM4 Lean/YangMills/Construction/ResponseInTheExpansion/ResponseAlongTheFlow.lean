import YangMills.Construction.ResponseInTheExpansion.ColdRegimeBounds
import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open RenormalizationStepParameters StepSettings TorusLumps WeightedResponses ClusterExpansionOfAStep StepReturn
def responseAlongFlowStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds → T.HoldsFrom ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound → ∀ M : ℝ,
      ∃ K : ResponseParameters, M ≤ K.Kc ∧ K.η₃ = T.η₃ ∧ K.N₀ = T.N 0 ∧ (∀ y : ℝ, K.Admissible (T.stepParameters y)) ∧
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ExpansionReturnsAt (T.stepParameters y) →
          (∀ β : ℝ, y ≤ β → HasExpansion (T.stepParameters y) 0 β (wilsonWeight β)) →
          ∀ (β : ℝ) (hL : ∀ c : ChainStage (T.stepParameters y), CoarseLabelFacts c.toStepSetup), y ≤ β →
            ∃ z₀ : StageWithResponse (T.stepParameters y), IsInitialStage T y β z₀ ∧
            ∀ t : ℕ, FlowStaysAbove (T.stepParameters y) β (t + 1) →
              StageOnFlow T K y β t (stagesFrom hL T.lam (couplingsAlongFlow (T.stepParameters y) β) z₀ t)
end YangMills.Construction.ResponseInTheExpansion
end
