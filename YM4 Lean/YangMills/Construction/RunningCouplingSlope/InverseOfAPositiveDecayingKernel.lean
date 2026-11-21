import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.DecayingKernels
def DecayingInverseBound : Prop :=
  ∀ M θ κ S : ℝ, 0 < M → 0 < θ → 0 < κ → 0 < S → ∃ M' θ' τ q : ℝ, 0 < M' ∧ 0 < θ' ∧ 0 < τ ∧ 0 ≤ q ∧ q < 1 ∧
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (d : ι → ι → ℝ) (T : Matrix ι ι ℝ),
      (∀ x, d x x = 0) → (∀ x y, 0 ≤ d x y) → (∀ x y, d x y = d y x) →
      (∀ x y z, d x z ≤ d x y + d y z) →
      (∀ x, ∑ y, Real.exp (-(θ / 2 * d x y)) ≤ S) →
      T.IsSymm → (∀ x y, |T x y| ≤ M * Real.exp (-(θ * d x y))) →
      (∀ ξ : ι → ℝ, κ * ∑ x, ξ x ^ 2 ≤ ∑ x, ∑ y, T x y * ξ x * ξ y) →
      ∃ G : Matrix ι ι ℝ, G * T = 1 ∧ T * G = 1 ∧
        (∀ x y, |G x y| ≤ M' * Real.exp (-(θ' * d x y))) ∧
        (∀ (k : ℕ) (x y : ι), |((1 - τ⁻¹ • T) ^ k) x y| ≤ q ^ k) ∧
        ∀ x y, HasSum (fun k : ℕ => τ⁻¹ * ((1 - τ⁻¹ • T) ^ k) x y) (G x y)
end YangMills.Construction.DecayingKernels
end
