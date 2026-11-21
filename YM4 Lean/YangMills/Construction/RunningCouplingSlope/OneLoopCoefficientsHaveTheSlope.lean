import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def StepSlopeCoefficientsHaveAverageSlope : Prop :=
  ∀ (g : ℝ) (L : ℕ), (∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = g ∧ T.side = L) →
    ∃ (b : ℕ → ℝ) (cH : ℝ), 0 ≤ cH ∧ AreStepSlopeCoefficients g L b ∧
      (∀ k : ℕ, |∑ l ∈ Finset.range k, b l - (k : ℝ) * CouplingFlow.slopeConst L| ≤ cH) ∧
      CouplingFlow.HasAverageSlope b (CouplingFlow.slopeConst L) cH
end YangMills.Construction.SlopeCoefficient
end
