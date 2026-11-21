import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TrajectoryData
def responseCoeffNearOneStatement : Prop :=
  ∀ a : ℝ, 1 ≤ a → ∃ (L₀ : ℕ) (rt₀ : RenormalizationStepParameters.ChainParameters → ℝ) (C₀ : ℝ), (∀ c, 0 < rt₀ c) ∧
    ∀ L : ℕ, Odd L → L₀ ≤ L →
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.coupling = a → T.side = L → T.Admissible → T.ColdStepHolds →
      T.HoldsFrom WeightedResponses.ColdRegimeEstimatesAt →
      T.rt ≤ rt₀ T.toChainParameters → C₀ ≤ T.derivBound →
      ∃ Kr : WeightedResponses.ResponseParameters, (∀ y : ℝ, Kr.Admissible (T.stepParameters y)) ∧
        ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → StepReturn.ExpansionReturnsAt (T.stepParameters y) →
        (∀ β : ℝ, y ≤ β → TorusLumps.HasExpansion (T.stepParameters y) 0 β (TorusLumps.wilsonWeight β)) →
        ∀ (β : ℝ) (k : ℕ), (∀ j ≤ k, y ≤ ResponseInTheExpansion.flowCouplings (T.stepParameters y) β j) →
          ∃ al : ℕ → ℝ, ResponseInTheExpansion.IsChainResponseCoeff (T.stepParameters y) Kr β k al ∧
            |al k - 1| ≤ 6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) *
              ResponseInTheExpansion.flowCouplings (T.stepParameters y) β k ^ (-(1 / 2) : ℝ) ∧
            6 * Kr.Cstar / (3 / 4 * CouplingFlow.slopeConst T.side) *
              ResponseInTheExpansion.flowCouplings (T.stepParameters y) β k ^ (-(1 / 2) : ℝ) ≤ 1 / 4
end YangMills.Construction.TrajectoryData
end
