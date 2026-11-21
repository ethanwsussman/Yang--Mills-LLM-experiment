import YangMills.Construction.ColdStepAtMirrorFrames.MeansFrozenOnCommonBondsFormForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def ConvexSmallGradientClassSegment : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (ρ m κ c : ℝ) (d : ι → ι → ℝ), 0 < ρ → 0 < m → m ≤ c →
    (∀ b, d b b = 0) →
    (∀ (A B : BondField ι → ℝ) (v : ℝ), IsConvexWithSmallGradient ρ m κ d A →
      IsConvexWithSmallGradient ρ m κ d B → 0 ≤ v → v ≤ 1 →
      IsConvexWithSmallGradient ρ m κ d (segmentInterpolant A B v)) ∧
    IsConvexWithSmallGradient ρ m κ d (fun η => c * ∑ b, ‖η b‖ ^ 2)
end YangMills.Construction.ColdStepAtMirrorFrames
end
