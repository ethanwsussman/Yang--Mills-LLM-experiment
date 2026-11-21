import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def zeroGaugeTotal : GaugeTotal := fun _ _ => 0
def addGaugeTotal (H H' : GaugeTotal) : GaugeTotal := fun n V => H n V + H' n V
def SlopeCoefficientAdditive : Prop :=
  (∀ H H' : GaugeTotal, ∀ b b' : ℝ, HasSlopeCoefficient Filter.atTop H b →
    HasSlopeCoefficient Filter.atTop H' b' →
    HasSlopeCoefficient Filter.atTop (addGaugeTotal H H') (b + b')) ∧
  HasSlopeCoefficient Filter.atTop zeroGaugeTotal 0 ∧
  ∀ (H H' : GaugeTotal) (n : ℕ), IsGaugeTotalAt (addGaugeTotal H H') n →
    IsGaugeTotalAt H n → IsGaugeTotalAt H' n
end YangMills.Construction.SlopeCoefficient
end
