import YangMills.Construction.SummableBoundsOfTheFlow.ScaledVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace ScaledVariables
def HaarGapLogTail : Prop :=
  ∀ s : ℝ, 0 < s → haarGap s = 3 / 2 * Real.log s + haarGapTail (1 / s)
end ScaledVariables
end YangMills.Construction
end
