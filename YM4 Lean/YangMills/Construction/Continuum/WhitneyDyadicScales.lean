import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WhitneyScales
def IsWhitneyRatio (c : ℝ) : Prop :=
  0 < c ∧ c ≤ 1 / 6
def whitneyRatio : ℝ := Classical.epsilon IsWhitneyRatio
theorem isWhitneyRatio_whitneyRatio : IsWhitneyRatio whitneyRatio :=
  Classical.epsilon_spec (p := IsWhitneyRatio) ⟨1 / 6, by norm_num, le_rfl⟩
def whitneyScale (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))
def whitneySide (j : ℕ) : ℝ := whitneyRatio * whitneyScale j
end YangMills.Construction.WhitneyScales
end
