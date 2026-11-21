import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigSpace
def seminormComparison : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ k q p : ℕ, max k q ≤ p → ∀ φ ∈ schwartzSet n,
      decaySeminorm k q φ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * schwartzSeminorm p φ) ∧
    (flatSchwartzSet n ⊆ schwartzSet n ∧
      ∃ W : Submodule ℂ (Config n → ℂ), (W : Set (Config n → ℂ)) = flatSchwartzSet n) ∧
    testFnOffDiag n ⊆ flatSchwartzSet n
end YangMills.Construction.ConfigSpace
end
