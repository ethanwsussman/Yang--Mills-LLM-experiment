import YangMills.Construction.RunningCouplingSlope.WaveSumsOfTheKernels
import Mathlib
set_option autoImplicit false
open Filter
noncomputable section
namespace YangMills.Construction.RunningCouplingSlope
def ChainKernelsAgreeOnLongWaves : Prop :=
  ∀ a : ℝ, 0 < a → ∀ (L : ℕ) [∀ n : ℕ, NeZero (2 * L ^ n)], Conventions.IsAdmissibleBlockingFactor L →
    ∀ k : ℕ, 1 ≤ k → ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
      ∃ C r : ℝ, 0 < r ∧ ∀ (n₀ : ℕ) (m : ℤ) (θ : ℝ), θ = 2 * Real.pi * m / (2 * (L : ℝ) ^ n₀) → |θ| < r →
        ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
          |chainCosineSum a ρ L n k θ - normaliserCosineSum L n k θ - differenceCosineSum a L n k θ| ≤
            C * |θ| ^ 3 + ε
end YangMills.Construction.RunningCouplingSlope
end
