import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def OneLoopCoefficientEqSlopeCoefficient : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ (t : ℕ) (b : ℝ),
    HasSlopeCoefficient Filter.atTop (stepGaugeTotal T.coupling T.ρA T.side t) b →
      ReferenceDensity.oneLoopCoefficient T.coupling T.ρA T.lam T.side t = b
end YangMills.Construction.SlopeCoefficient
end
