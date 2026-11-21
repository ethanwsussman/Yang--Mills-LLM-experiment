import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
namespace ColdStepAtMirrorFrames
def HaarGapOfNormNearOne : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ (P : Type) [NormedAddCommGroup P] [NormedSpace ℝ P] (M : P → ℍ[ℝ]) (A : ℝ),
    2 ≤ A → ContDiffAt ℝ 3 M 0 → 1 / 2 ≤ ‖M 0‖ → ‖M 0‖ ≤ 1 →
    ContDiffAt ℝ 3 (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) 0 ∧
    ∀ u v : P,
      |fderiv ℝ (fun ζ => haarGap (A * ‖M ζ‖) - haarGap A) 0 u| ≤ K * ‖fderiv ℝ M 0 u‖ ∧
      |fderiv ℝ (fun ζ => fderiv ℝ (fun ξ => haarGap (A * ‖M ξ‖) - haarGap A) ζ u) 0 v| ≤
        K * (‖fderiv ℝ M 0 u‖ * ‖fderiv ℝ M 0 v‖ + ‖fderiv ℝ (fun ζ => fderiv ℝ M ζ u) 0 v‖)
end ColdStepAtMirrorFrames
end YangMills.Construction
end
