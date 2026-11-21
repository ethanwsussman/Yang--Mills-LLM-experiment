import YangMills.Construction.RunningCouplingSlope.TotalsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def MinimalActionHasUnitCoefficient : Prop :=
  ∀ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible → ∀ t : ℕ,
    SlopeCoefficient.HasSlopeCoefficient Filter.atTop (minimalActionTotal T.coupling T.side t) 1
end YangMills.Construction.RunningCouplingSlope
end
