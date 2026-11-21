import YangMills.Construction.RunningCouplingSlope.TotalOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open SlopeCoefficient
def StepGaugeTotalsHaveSlopeCoefficients : Prop :=
  ∀ (g : ℝ) (L : ℕ), (∃ T : RenormalizationStepParameters.ParameterAssignment, T.Admissible ∧ T.coupling = g ∧ T.side = L) →
    ∀ t : ℕ, ∃ b : ℝ, ∀ r : ℝ, 0 < r → r ≤ 1 →
      HasSlopeCoefficient Filter.atTop (stepGaugeTotal g r L t) b
end YangMills.Construction.RunningCouplingSlope
end
