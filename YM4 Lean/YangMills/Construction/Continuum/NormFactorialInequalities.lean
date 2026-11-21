import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ElementaryInequalities
noncomputable def euclidNorm {D : ℕ} (w : Fin D → ℝ) : ℝ :=
  ‖(WithLp.toLp 2 w : EuclideanSpace ℝ (Fin D))‖
def NormPowerFactorialBounds : Prop :=
  (∀ (D : ℕ), 1 ≤ D → ∀ w : Fin D → ℝ,
    ‖w‖ ≤ euclidNorm w ∧ euclidNorm w ≤ Real.sqrt (D : ℝ) * ‖w‖) ∧
  (∀ (s : ℕ) (v : ℝ), 0 ≤ v → v ^ s ≤ (s.factorial : ℝ) * Real.exp v) ∧
  (∀ (s : ℕ), 1 ≤ s → ∀ k : Fin s → ℕ,
    ∏ a, (k a).factorial ≤ (∑ a, k a).factorial)
end YangMills.Construction.ElementaryInequalities
