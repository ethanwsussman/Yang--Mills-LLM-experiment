import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace YangMills.Construction.ColdStepAtMirrorFrames
def QuaternionCutoffSmoothBounded : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p →
    ContDiff ℝ ∞ (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖) ∧
      ∀ j : ℕ, ∃ B : ℝ, ∀ v : ℍ[ℝ], ‖iteratedFDeriv ℝ j (fun v : ℍ[ℝ] => cutoffFactor ρ p ‖v‖) v‖ ≤ B
end YangMills.Construction.ColdStepAtMirrorFrames
end
