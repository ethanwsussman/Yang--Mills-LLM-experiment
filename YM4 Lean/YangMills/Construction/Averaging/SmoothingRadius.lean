import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Averaging
def IsSmoothingRadius (L : ℕ) (ω : ℝ) : Prop :=
  0 < ω ∧ ω ≤ 1 / (200 * (L : ℝ) ^ 2)
def smoothingRadius (L : ℕ) : ℝ := Classical.epsilon (IsSmoothingRadius L)
theorem isSmoothingRadius_smoothingRadius {L : ℕ} (_hL_odd : Odd L) (hL : 13 ≤ L) :
    IsSmoothingRadius L (smoothingRadius L) := by
  exact Classical.epsilon_spec (p := IsSmoothingRadius L)
    ⟨1 / (200 * (L : ℝ) ^ 2), by positivity, le_rfl⟩
end YangMills.Construction.Averaging
end
