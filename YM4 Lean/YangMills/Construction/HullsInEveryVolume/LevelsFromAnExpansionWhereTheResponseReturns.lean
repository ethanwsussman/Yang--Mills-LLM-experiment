import YangMills.Construction.ResponseInTheExpansion.LevelsOfAFlow
import YangMills.Construction.ResponseInTheExpansion.RunningCouplingSlope
import YangMills.Construction.ResponseInTheExpansion.TheResponseReturns
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullTrees
def stagesFromReturningExpansionStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ), (∀ c, 0 < rt₀ c) ∧ ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.rt ≤ rt₀ T.toChainParameters →
      ∃ M : ℝ, ∀ K : WeightedResponses.ResponseParameters, M ≤ K.Kc → K.N₀ = T.N 0 →
        (∀ y : ℝ, K.Admissible (T.stepParameters y)) →
        (∃ Cs y₁ : ℝ, 0 ≤ Cs ∧ ∀ y : ℝ, y₁ ≤ y → WeightedResponses.ReturnsAtParameters T K Cs y) →
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
          (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) →
          ∀ (β : ℝ) (hL : ∀ c : WeightedResponses.ChainStage (T.stepParameters y), ClusterExpansionOfAStep.CoarseLabelFacts c.toStepSetup)
            (z₀ : ResponseInTheExpansion.StageWithResponse (T.stepParameters y)),
            y ≤ β → ResponseInTheExpansion.IsInitialStage T y β z₀ → z₀.2.responseParams = K →
            z₀.1.toStepSetup.HasExpansions →
            ∀ t : ℕ, WeightedResponses.FlowStaysAbove (T.stepParameters y) β (t + 1) →
              ResponseInTheExpansion.StageOnFlow T K y β t
                (ResponseInTheExpansion.stagesFrom hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ t)
end YangMills.Construction.HullTrees
end
