import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LandauKolmogorovAtZero : Prop :=
  ∀ p j : ℕ, j < p → ∃ C : ℝ, 0 < C ∧ ∀ (g : ℕ → ℝ → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp →
    (∀ i, i < p → ∀ s, |s| ≤ τ₀ → HasDerivAt (g i) (g (i + 1) s) s) →
    (∀ s, |s| ≤ τ₀ → |g 0 s| ≤ M₀) → (∀ s, |s| ≤ τ₀ → |g p s| ≤ Mp) →
    |g j 0| ≤ C * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / p) * Mp ^ ((j : ℝ) / p))
end YangMills.Construction.ColdStepAtMirrorFrames
end
