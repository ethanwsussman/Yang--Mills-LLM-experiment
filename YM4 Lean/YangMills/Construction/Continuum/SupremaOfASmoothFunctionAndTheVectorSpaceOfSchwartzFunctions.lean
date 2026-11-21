import YangMills.Construction.Continuum.ConjLinearSeminormInnerForm
import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
def multiIndexDecaySup {n : ℕ} (k : ℕ) (α : MultiIndex n) (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ x : Config n, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖)
def SchwartzSupremaStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ φ : Config n → ℂ, ContDiff ℝ ∞ φ →
      (IsSchwartz φ ↔ ∀ k : ℕ, 1 ≤ k → schwartzSeminorm k φ < ⊤)) ∧
    (∀ φ φ' : Config n → ℂ, ContDiff ℝ ∞ φ → ContDiff ℝ ∞ φ' → ∀ (c c' : ℂ) (k k' : ℕ), k ≤ k' →
      schwartzSeminorm k φ ≤ schwartzSeminorm k' φ ∧
      ContDiff ℝ ∞ (c • φ + c' • φ') ∧
      ∀ α : MultiIndex n, iteratedPartial α (c • φ + c' • φ') =
        c • iteratedPartial α φ + c' • iteratedPartial α φ') ∧
    (∀ φ φ' : Config n → ℂ, IsSchwartz φ → IsSchwartz φ' → ∀ c c' : ℂ,
      (∀ k : ℕ, schwartzSeminorm k φ < ⊤) ∧ IsSchwartz (c • φ + c' • φ')) ∧
    (∀ φ : Config n → ℂ, ContDiff ℝ ∞ φ → ∀ k q : ℕ,
      schwartzSeminorm k φ ≤ decaySeminorm k k φ ∧
      decaySeminorm k q φ ≤ ENNReal.ofReal (2 ^ ((k : ℝ) / 2)) * schwartzSeminorm (max k q) φ) ∧
    (∀ φ : Config n → ℂ, ContDiff ℝ ∞ φ →
      (IsSchwartz φ ↔ ∀ (k : ℕ) (α : MultiIndex n), multiIndexDecaySup k α φ < ⊤)) ∧
    ∃ S : Submodule ℂ (Config n → ℂ), (S : Set (Config n → ℂ)) = {φ | IsSchwartz φ} ∧
      (∀ k : ℕ, (∀ φ : S, schwartzSeminorm k φ.1 < ⊤) ∧
        Continuum.IsComplexSeminorm fun φ : S => (schwartzSeminorm k φ.1).toReal) ∧
      (∀ k q : ℕ, (∀ φ : S, decaySeminorm k q φ.1 < ⊤) ∧
        Continuum.IsComplexSeminorm fun φ : S => (decaySeminorm k q φ.1).toReal)
end YangMills.Construction.ConfigSpace
end
