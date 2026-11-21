import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def IsSchwartzSeminorm {n : ℕ} (ν : (Config n → ℂ) → ℝ≥0∞) : Prop :=
  (∀ φ ∈ schwartzSet n, ν φ < ⊤) ∧
  (∀ (c : ℂ), ∀ φ ∈ schwartzSet n, ν (c • φ) = ENNReal.ofReal ‖c‖ * ν φ) ∧
  ∀ φ ∈ schwartzSet n, ∀ ψ ∈ schwartzSet n, ν (φ + ψ) ≤ ν φ + ν ψ
def schwartzSeminormsFinite : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ k q p : ℕ,
    (∀ φ ∈ schwartzSet n, decaySeminorm k q φ < ⊤ ∧ sobolevWeightNorm p φ ≤ decaySeminorm p p φ) ∧
    IsSchwartzSeminorm (decaySeminorm (n := n) k q) ∧
    IsSchwartzSeminorm (sobolevWeightNorm (n := n) p)
end YangMills.Construction.ConfigurationSpace
end
