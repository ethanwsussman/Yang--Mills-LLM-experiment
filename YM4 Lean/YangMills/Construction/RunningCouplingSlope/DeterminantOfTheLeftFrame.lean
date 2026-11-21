import YangMills.Construction.RunningCouplingSlope.TangentsOfAChartPoint
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open BlockAverages
def LeftExpDifferentialDet : Prop :=
  ∀ w : imaginaryQuaternions, (leftExpDifferential w).det = Real.sinc ‖w‖ ^ 2
end YangMills.Construction.RunningCouplingSlope
end
