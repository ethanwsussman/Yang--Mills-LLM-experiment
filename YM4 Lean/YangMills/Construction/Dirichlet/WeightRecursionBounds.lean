import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
namespace Dirichlet
def WeightRecursionBounds : Prop :=
  ∀ L : ℕ, 3 ≤ L → Odd L → ∀ w : ℕ → ℝ, w 0 = 1 → w 1 = 1 →
    (∀ k : ℕ, 1 ≤ k → w (k + 1) = w k / ((L : ℝ) ^ (-2 : ℤ) + w k)) →
    (∀ k : ℕ, 1 ≤ k →
        w k = (1 - (L : ℝ) ^ (-2 : ℤ)) / (1 - (L : ℝ) ^ (-(2 * (k : ℤ))))) ∧
      ∀ k : ℕ, 1 - (L : ℝ) ^ (-2 : ℤ) < w k ∧ w k ≤ 1
end Dirichlet
end YangMills.Construction
