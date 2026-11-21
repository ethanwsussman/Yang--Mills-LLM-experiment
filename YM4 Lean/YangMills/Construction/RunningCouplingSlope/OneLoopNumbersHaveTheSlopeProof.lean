import YangMills.Construction.RunningCouplingSlope.OneLoopCoefficientsHaveTheSlope
import YangMills.Construction.RunningCouplingSlope.OneLoopNumberIsTheCoefficient
import YangMills.Construction.RunningCouplingSlope.OneLoopNumbersHaveTheSlope
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open SlopeCoefficient
theorem oneLoopCoefficientsHaveAverageSlope_of_stepSlope (hslope : StepSlopeCoefficientsHaveAverageSlope)
    (heq : OneLoopCoefficientEqSlopeCoefficient) : OneLoopCoefficientsHaveAverageSlope := by
  intro g L hT
  obtain ⟨b, cH, hc, hb, _, hs⟩ := hslope g L hT
  refine ⟨cH, hc, ?_⟩
  rintro T hA rfl rfl
  obtain ⟨-, -, -, hr, hr1, -⟩ := hA.chain
  have hfun : ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side = b :=
    funext fun t => heq T hA t (b t) (hb t T.ρA hr hr1)
  rw [hfun]
  exact hs
end YangMills.Construction.RunningCouplingSlope
end
