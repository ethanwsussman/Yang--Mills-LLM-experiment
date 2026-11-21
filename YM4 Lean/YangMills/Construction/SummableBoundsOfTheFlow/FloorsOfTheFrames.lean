import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
def frameRadiusGrowthStatement : Prop :=
  ∀ A c : ℝ, 0 < A → 0 < c → ∃ y : ℝ, 1 ≤ y ∧ ∀ x : ℝ, y ≤ x →
    A * x ^ 2 * Real.exp (-(c * frameRadius x)) ≤ 1 ∧ A ≤ frameRadius x
end Estimates
end YangMills.Construction
end
