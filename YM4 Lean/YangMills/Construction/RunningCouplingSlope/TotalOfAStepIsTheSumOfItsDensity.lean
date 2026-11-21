import YangMills.Construction.RunningCouplingSlope.DensityOfTheStepAtParameters
import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages TorusFields RenormalizationStepParameters SlopeCoefficient
namespace RunningCouplingSlope
def StepTotalEqDensitySum : Prop :=
  ∀ T : ParameterAssignment, T.Admissible → ∀ (t n : ℕ) [NeZero n] (V : TorusField n), 64 ≤ n →
    IsCold (9 / 8 * T.threshold) V →
    centeredDensityTotal (paramStepDensity T t) n V = stepGaugeTotal T.coupling T.ρA T.side t n V
end RunningCouplingSlope
end YangMills.Construction
end
