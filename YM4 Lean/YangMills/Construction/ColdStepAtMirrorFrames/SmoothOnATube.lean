import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def UniformDerivBoundNearCompact : Prop :=
  ∀ (k : ℕ) (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : (Fin k → ℝ) × E → ℝ) (S : Set E),
    IsCompact S → (∀ y ∈ S, ContDiffAt ℝ 3 f (0, y)) →
    ∃ r C : ℝ, 0 < r ∧ ∀ y ∈ S, ContDiffOn ℝ 3 (fun t => f (t, y)) (Metric.ball 0 r) ∧
      ∀ j, j ≤ 3 → ∀ t ∈ Metric.ball (0 : Fin k → ℝ) r,
        ‖iteratedFDeriv ℝ j (fun t => f (t, y)) t‖ ≤ C
end YangMills.Construction.ColdStepAtMirrorFrames
end
