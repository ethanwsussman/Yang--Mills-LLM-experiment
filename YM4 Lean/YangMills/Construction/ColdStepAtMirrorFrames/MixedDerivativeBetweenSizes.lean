import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ColdStepAtMirrorFrames
def LandauKolmogorovMultivariateAtZero : Prop :=
  ∀ (k p j : ℕ), j < p → ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin k → ℝ) → ℝ) (τ₀ M₀ Mp : ℝ), 0 < τ₀ → 0 < M₀ → 0 ≤ Mp →
    ContDiff ℝ p u → (∀ τ, ‖τ‖ ≤ τ₀ → |u τ| ≤ M₀) → (∀ τ, ‖τ‖ ≤ τ₀ → ‖iteratedFDeriv ℝ p u τ‖ ≤ Mp) →
    (∀ (σ : Equiv.Perm (Fin j)) (m : Fin j → (Fin k → ℝ)),
      iteratedFDeriv ℝ j u 0 (m ∘ σ) = iteratedFDeriv ℝ j u 0 m) →
    ∀ v : Fin j → (Fin k → ℝ), (∀ l, ‖v l‖ ≤ 1) →
      |iteratedFDeriv ℝ j u 0 v| ≤ C * (M₀ / τ₀ ^ j + M₀ ^ (1 - (j : ℝ) / p) * Mp ^ ((j : ℝ) / p))
end YangMills.Construction.ColdStepAtMirrorFrames
end
