import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ExistsCutoff : Prop := ∀ ρ : ℝ, 0 < ρ → ∃ p : ℝ → ℝ, IsCutoff ρ p
end YangMills.Construction.ColdStepAtMirrorFrames
end
