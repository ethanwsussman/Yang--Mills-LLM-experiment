import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HaarDensity
open ColdStepAtMirrorFrames
def logHaarDensityContDiffOnBall : Prop :=
  ∀ v : EuclideanSpace ℝ (Fin 3), ‖v‖ < Real.pi →
    ContDiffAt ℝ 3 (fun w => Real.log (haarLogDensity w)) v
end YangMills.Construction.HaarDensity
end
