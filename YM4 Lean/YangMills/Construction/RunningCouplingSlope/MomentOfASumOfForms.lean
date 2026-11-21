import YangMills.Construction.RunningCouplingSlope.MomentOfATotal
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
open TorusFields
def formFamilyMomentStatement : Prop :=
  ∀ v : ℝ, 0 < v → v ≤ 1 → ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) [NeZero n] (M₀ : ℝ) (H : TorusSite n → TorusBond n → TorusBond n → ℝ),
    64 ≤ n → 0 ≤ M₀ → IsDecayingFormFamily M₀ v H →
      |kernelSecondMoment (fun c c' => ∑ Y, H Y c c') - formOnLinearPotential (momentCutoff n) (H 0)| ≤
        C * M₀ * Real.exp (-(v * (n : ℝ) / 64))
end YangMills.Construction.RunningCouplingSlope
end
