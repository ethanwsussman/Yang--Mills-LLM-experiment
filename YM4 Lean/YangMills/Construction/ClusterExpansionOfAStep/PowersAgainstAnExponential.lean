import YangMills.Construction.ClusterExpansionOfAStep.EffectiveDensityOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TorusLumps
def PolynomialBelowExponential : Prop :=
  ∀ (a κ B : ℝ) (p q : ℕ), 0 < κ → 0 < B → ∃ y₀ : ℝ, 1 ≤ y₀ ∧ ∀ x : ℝ, y₀ ≤ x → ∀ k : ℕ,
    (clusterRange x : ℝ) / B ≤ k → a * x ^ p * ((k : ℝ) + 1) ^ q * Real.exp (-(κ * k)) ≤ 1
end YangMills.Construction.TorusLumps
end
