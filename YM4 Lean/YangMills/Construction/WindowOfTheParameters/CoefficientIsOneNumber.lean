import YangMills.Construction.RunningCouplingSlope.CoefficientOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.SlopeCoefficient
def SlopeCoefficientUnique : Prop :=
  ∀ (l : Filter ℕ) [l.NeBot] (H : GaugeTotal) (b b' : ℝ),
    HasSlopeCoefficient l H b → HasSlopeCoefficient l H b' → b = b'
end YangMills.Construction.SlopeCoefficient
end
