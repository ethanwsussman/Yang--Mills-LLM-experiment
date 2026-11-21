import YangMills.Construction.Continuum.SchwartzFunctionsFlatOutsideAnOpenSet
import Mathlib
set_option autoImplicit false
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.ConfigSpace
def orderedPosTimeSet (n : ℕ) : Set (Config n) :=
  {x | (∀ i, 0 < argTime x i) ∧ StrictMono (argTime x)}
def VanishingOnOpenProperties : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (∀ (U : Set (Config n)) (φ : Config n → ℂ), IsOpen U → ContDiff ℝ ∞ φ →
      (∀ x ∈ U, φ x = 0) → FlatOn φ (closure U)) ∧
    (∀ φ ∈ schwartzFlatOffDiagonal n, (∀ (x : Config n) (i : Fin n), argTime x i < 0 → φ x = 0) →
      φ ∈ schwartzFlatOffPosTime n) ∧
    (orderedPosTimeSet n ⊆ posTimeSet n ∧
      ∀ φ : Config n → ℂ, IsSchwartz φ → (∀ x, x ∉ orderedPosTimeSet n → φ x = 0) →
        φ ∈ schwartzFlatOffPosTime n)
end YangMills.Construction.ConfigSpace
end
