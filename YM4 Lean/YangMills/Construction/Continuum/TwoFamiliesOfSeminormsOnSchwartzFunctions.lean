import YangMills.Construction.Continuum.TestFunctionsOfConfigurationSpace
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
def sobolevWeightNormFamily (n : ℕ) : ℕ → schwartzSet n → ℝ≥0∞ :=
  fun p φ => sobolevWeightNorm p φ.1
def SeminormFamiliesComparison : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ k q p : ℕ, max k q ≤ p → ∀ φ ∈ schwartzSet n,
      decaySeminorm k q φ ≤ ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * sobolevWeightNorm p φ) ∧
    ((∃ t : TopologicalSpace (schwartzSet n),
        ∀ U : Set (schwartzSet n), @IsOpen _ t U ↔ U ∈ schwartzOpenSets n) ∧
      GeneratesSchwartzTopology (decaySeminormFamily n) ∧
      GeneratesSchwartzTopology (sobolevWeightNormFamily n)) ∧
    ((flatSchwartzSet n ⊆ schwartzSet n ∧
        IsLinearFunctionSet (flatSchwartzSet n)) ∧
      IsSchwartzClosed {φ : schwartzSet n | φ.1 ∈ flatSchwartzSet n}) ∧
    offDiagonalTestSet n ⊆ flatSchwartzSet n
end YangMills.Construction.ConfigurationSpace
end
