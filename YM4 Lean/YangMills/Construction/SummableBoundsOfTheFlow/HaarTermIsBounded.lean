import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages ColdStepAtMirrorFrames
namespace Estimates
def haarLogRatioBoundStatement : Prop :=
  ∀ w : imaginaryQuaternions, ‖w‖ ≤ 1 → |haarLogRatio w| ≤ 1
end Estimates
end YangMills.Construction
end
