import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open YangMills.Construction.StepSettings YangMills.Construction.SlopeCoefficient
namespace RunningCouplingSlope
def laplaceRemainder (R : StepSetup) : GaugeTotal := fun n V =>
  goodFieldLogIntegral R n V + R.coupling * minimalActionTotal R.params.coupling R.params.side (R.depth + 1) n V
def densityAtMinimizer (R : StepSetup) : GaugeTotal :=
  atMinimizer R.params.coupling R.anchorRadius R.params.side R.depth (centeredDensityTotal R.density)
def stepTorusSide (n₀ : ℕ) (C₁ x : ℝ) : ℕ := n₀ + ⌊C₁ * Real.log x⌋₊
end RunningCouplingSlope
end YangMills.Construction
end
