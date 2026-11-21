import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.AdmissibleConstants
def GridOffsetAvoidsPoints : Prop :=
  ∀ (a l ε : ℝ) (m n : ℕ), 0 < a → 0 < ε → l = m * a → (n : ℝ) * (6 * ε / a + 1) < m →
    ∀ α : Fin n → ℝ, ∃ j : ℤ, ∀ (i : Fin n) (k : ℤ),
      3 * ε ≤ |α i - (a * ((j : ℝ) + 1 / 2) + l * k)|
end YangMills.Construction.AdmissibleConstants
end
