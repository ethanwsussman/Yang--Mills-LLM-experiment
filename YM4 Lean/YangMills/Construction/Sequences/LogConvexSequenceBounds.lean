import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.LogConvexSequence
def RatioAndPowerBounds : Prop :=
  ∀ x : ℕ → ℝ, (∀ n, 0 ≤ x n) → (∀ n, 1 ≤ n → x n ^ 2 ≤ x (n - 1) * x (n + 1)) →
    (∀ n, x 1 * x n ≤ x 0 * x (n + 1)) ∧ ∀ n, 1 ≤ n → x 1 ^ n ≤ x 0 ^ (n - 1) * x n
end YangMills.Construction.LogConvexSequence
