import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def HaarGapDerivBound : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → |s ^ k * iteratedDeriv k haarGap s| ≤ C
end ColdStepAtMirrorFrames
end YangMills.Construction
end
