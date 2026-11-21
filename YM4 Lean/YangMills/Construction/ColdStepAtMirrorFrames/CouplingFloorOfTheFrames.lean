import YangMills.Construction.ColdStepAtMirrorFrames.ColdStepEstimate
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def CouplingThreshold : Prop :=
  ∀ (Cf C δ₂ κ σ : ℝ) (N : ℕ), 0 < δ₂ → 0 < κ → κ ≤ δ₂ / 2 ^ 14 → 0 < σ →
    ∃ y₀ : ℝ, ∀ x : ℝ, y₀ ≤ x →
      N ≤ frameRadius x ∧ 16 ≤ frameRadius x ∧
      Cf * Real.exp (-(δ₂ / 4 * frameRadius x)) ≤ 2⁻¹ ^ 10 * σ ∧
      C * x ^ 2 * (Cf * Real.exp (-(δ₂ / 4 * frameRadius x))) ≤
        Real.exp (-(2 ^ 10 * κ * frameRadius x)) ∧
      C * x ^ 2 * Real.exp (-(2 * δ₂ * frameRadius x)) ≤ 1 ∧
      Cf * Real.exp (-(δ₂ / 4 * frameRadius x)) ≤ x ^ (-(1 / 2 : ℝ))
end YangMills.Construction.ColdStepAtMirrorFrames
end
