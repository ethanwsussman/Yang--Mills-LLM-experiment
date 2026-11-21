import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Calculus
def DerivDiffBoundOfClose : Prop :=
  ∀ (f₁ f₂ f₁' f₂' f₁'' f₂'' : ℝ → ℝ) (h M₀ M₂ : ℝ), 0 < h →
    (∀ t ∈ Set.Icc 0 h, HasDerivAt f₁ (f₁' t) t) → (∀ t ∈ Set.Icc 0 h, HasDerivAt f₂ (f₂' t) t) →
    (∀ t ∈ Set.Icc 0 h, HasDerivAt f₁' (f₁'' t) t) → (∀ t ∈ Set.Icc 0 h, HasDerivAt f₂' (f₂'' t) t) →
    (∀ t ∈ Set.Icc 0 h, |f₁'' t| ≤ M₂) → (∀ t ∈ Set.Icc 0 h, |f₂'' t| ≤ M₂) →
    |f₁ 0 - f₂ 0| ≤ M₀ → |f₁ h - f₂ h| ≤ M₀ →
    |f₁' 0 - f₂' 0| ≤ 2 * M₀ / h + 2 * M₂ * h
end YangMills.Construction.Calculus
end
