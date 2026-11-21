import YangMills.Construction.SummableBoundsOfTheFlow.FlowOfTheNumbers
import YangMills.Construction.SummableBoundsOfTheFlow.ReferenceTrajectoryOfTheFlow
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def OneLoopCoefficientsHaveAverageSlope : Prop :=
  ∀ (g : ℝ) (L : ℕ), (∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = g ∧ T.side = L) →
    ∃ cH : ℝ, 0 ≤ cH ∧
    ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → T.coupling = g → T.side = L →
      CouplingFlow.HasAverageSlope (ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side)
        (CouplingFlow.slopeConst L) cH
end YangMills.Construction.SlopeCoefficient
end
