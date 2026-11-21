import YangMills.Construction.ColdStepAtMirrorFrames.IntegrandOfTheColdStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
open ColdStepAtMirrorFrames
namespace Estimates
def cutoffDerivBoundsStatement : Prop :=
  ∀ (ρ : ℝ) (p : ℝ → ℝ), 0 < ρ → IsCutoff ρ p →
    (∀ u, 0 < u → u < ρ → 0 ≤ deriv p u) ∧
    (∀ u, 0 < u → u < 5 * ρ / 8 → ∀ j : ℕ, 1 ≤ j → iteratedDeriv j p u = 0) ∧
    (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u, 0 < u → u < ρ → (1 + deriv p u) ^ k * Real.exp (-p u) ≤ C) ∧
    (∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ u, 0 < u → u < ρ →
      deriv (deriv p) u ≤ ε * deriv p u ^ 2 + C) ∧
    (∀ j : ℕ, 1 ≤ j → ∃ (C : ℝ) (k : ℕ), 0 ≤ C ∧ ∀ u, 0 < u → u < ρ →
      |iteratedDeriv j p u| ≤ C * (1 + deriv p u) ^ k) ∧
    ∃ D : ℝ, 0 ≤ D ∧ ∀ u, 0 < u → u < ρ → (ρ - u)⁻¹ ≤ D * (1 + deriv p u)
end Estimates
end YangMills.Construction
end
