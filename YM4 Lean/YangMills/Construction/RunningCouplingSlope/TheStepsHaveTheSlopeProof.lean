import YangMills.Construction.RunningCouplingSlope.NumberOfAStepIsTheNumberOfItsDensity
import YangMills.Construction.RunningCouplingSlope.OneLoopCoefficientsHaveTheSlope
import YangMills.Construction.RunningCouplingSlope.OneLoopNumberIsTheCoefficient
import YangMills.Construction.RunningCouplingSlope.TheStepsHaveTheSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open YangMills.Construction.SlopeCoefficient YangMills.Construction.ReferenceDensity
theorem stepCoefficientsHaveSlope_of_densityValue (h₁ : StepSlopeCoefficientsHaveAverageSlope)
    (h₂ : OneLoopCoefficientEqSlopeCoefficient)
    (h₃ : StepCoefficientEqualsDensityValue) :
    StepCoefficientsHaveSlope := by
  rintro a L ⟨T, hT, rfl, rfl⟩
  obtain ⟨-, -, -, hρ0, hρ1, -⟩ := hT.chain
  obtain ⟨b, cH, hc, hb, hsum, hslope⟩ := h₁ T.coupling T.side ⟨T, hT, rfl, rfl⟩
  refine ⟨b, cH, hc, fun t => ?_, hsum, hslope⟩
  obtain ⟨v, hv, -, hs⟩ := h₃ T hT t
  have e₁ : oneLoopCoefficient T.coupling T.ρA T.lam T.side t = b t :=
    h₂ T hT t (b t) (hb t T.ρA hρ0 hρ1)
  have e₂ : oneLoopCoefficient T.coupling T.ρA T.lam T.side t = v := hs.tsum_eq
  rw [← e₁, e₂]
  exact hv
end YangMills.Construction.RunningCouplingSlope
end
