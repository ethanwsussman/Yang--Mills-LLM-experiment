import YangMills.Construction.RunningCouplingSlope.NumberOfAStep
import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def IsAdmissibleParametersAt (a : ℝ) (L : ℕ) : Prop :=
  ∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = a ∧ T.side = L
def StepCoefficientsHaveSlope : Prop :=
  ∀ (a : ℝ) (L : ℕ), IsAdmissibleParametersAt a L → ∃ (b : ℕ → ℝ) (cH : ℝ), 0 ≤ cH ∧
    AreStepCoefficients a L b ∧
    (∀ k : ℕ, |∑ l ∈ Finset.range k, b l - (k : ℝ) * CouplingFlow.slopeConst L| ≤ cH) ∧
    CouplingFlow.HasAverageSlope b (CouplingFlow.slopeConst L) cH
end YangMills.Construction.RunningCouplingSlope
end
