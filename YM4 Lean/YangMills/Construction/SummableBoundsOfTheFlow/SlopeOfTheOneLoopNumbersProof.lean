import YangMills.Construction.RunningCouplingSlope.OneLoopNumbersHaveTheSlope
import YangMills.Construction.SummableBoundsOfTheFlow.SlopeOfTheOneLoopNumbers
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.OneLoopSlope
theorem oneLoopCoefficientsHaveSlope_of_averageSlope
    (h : SlopeCoefficient.OneLoopCoefficientsHaveAverageSlope) :
    OneLoopCoefficientsHaveSlope := by
  intro a ha L hodd hL
  by_cases hT : ∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = a ∧ T.side = L
  · obtain ⟨c, -, hc⟩ := h a L hT
    exact ⟨c, hc⟩
  · exact ⟨0, fun T hD hTa hTL => absurd ⟨T, hD, hTa, hTL⟩ hT⟩
end YangMills.Construction.OneLoopSlope
end
