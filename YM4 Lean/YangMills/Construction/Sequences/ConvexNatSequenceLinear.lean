import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.ConvexNatSequence
def LinearOfConvexBoundedDivisible : Prop :=
  ∀ f : ℕ → ℕ,
    f 0 = 0 →
    (∀ k : ℕ, 1 ≤ k → 2 * f k ≤ f (k - 1) + f (k + 1)) →
    (∃ C : ℝ, ∀ k : ℕ, (f k : ℝ) ≤ C * (k : ℝ)) →
    (∀ k : ℕ, 1 ≤ k → k ∣ 2 * f k) →
    ∀ k : ℕ, f k = k * f 1
end YangMills.Construction.ConvexNatSequence
