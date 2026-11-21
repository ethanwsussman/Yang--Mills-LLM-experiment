import YangMills.Construction.ColdStepAtMirrorFrames.ConvexMeasuresOnBalls
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace BallExtensions
open YangMills.Construction.ColdStepAtMirrorFrames
def ContDiffExtensionNearBalls : Prop :=
  ∀ (ι : Type) [Fintype ι] (ρ : ℝ) (k : ℕ) (g : BondField ι → ℝ) (U : Set (BondField ι)),
    0 < ρ → IsOpen U → (∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → η ∈ U) → ContDiffOn ℝ k g U →
    ∃ g' : BondField ι → ℝ, ContDiff ℝ k g' ∧
      ∀ η : BondField ι, (∀ b, ‖η b‖ ≤ ρ) → g' =ᶠ[nhds η] g
end BallExtensions
end YangMills.Construction
end
