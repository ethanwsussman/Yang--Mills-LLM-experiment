import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepIsLocal
import YangMills.Construction.RunningCouplingSlope.NumberOfALocalDensity
import YangMills.Construction.RunningCouplingSlope.OneLoopNumberIsTheCoefficient
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
theorem oneLoopCoefficientEqSlopeCoefficient_of_localDensity (hcoef : CoefficientFromDensity.Claim)
    (hloc : StepDensityIsLocal.Claim) : SlopeCoefficient.OneLoopCoefficientEqSlopeCoefficient := by
  intro T hT t b hb
  obtain ⟨hl, hs⟩ := hloc T hT t
  have h := hcoef _ _ b hl hb hs
  exact h.tsum_eq
end YangMills.Construction.RunningCouplingSlope
end
