import YangMills.Construction.ColdStepAtMirrorFrames.FixedVariablesOfTheStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open BlockAverages
namespace ColdStepAtMirrorFrames
def HaarLogRatioNearZero : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ContDiffAt ℝ 3 haarLogRatio v ∧
    (∀ e : imaginaryQuaternions, |fderiv ℝ haarLogRatio v e| ≤ C * ‖e‖) ∧
    ∀ e e' : imaginaryQuaternions, |fderiv ℝ (fun z => fderiv ℝ haarLogRatio z e) v e'| ≤ C * ‖e‖ * ‖e'‖
end ColdStepAtMirrorFrames
end YangMills.Construction
end
