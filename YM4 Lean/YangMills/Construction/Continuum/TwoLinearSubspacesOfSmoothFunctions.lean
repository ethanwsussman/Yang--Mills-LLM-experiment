import YangMills.Construction.Continuum.FlatSchwartzAndTuples
import Mathlib
noncomputable section
namespace YangMills.Construction.ConfigSpace
open SmoothMaps
def IsFunctionSubspace {n : ℕ} (S : Set (Config n → ℂ)) : Prop :=
  ∃ M : Submodule ℂ (Config n → ℂ), (M : Set (Config n → ℂ)) = S
def smoothFlatOnDiagonal (n : ℕ) : Set (Config n → ℂ) :=
  {φ | φ ∈ smoothSet (Config n) ∧
    ∀ x ∈ diagonalSet n, ∀ α : MultiIndex n, iteratedPartial α φ x = 0}
def SmoothSubspacesStatement : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    IsFunctionSubspace (smoothSet (Config n)) ∧
    (schwartzSet n ⊆ smoothSet (Config n) ∧ IsFunctionSubspace (schwartzSet n)) ∧
    (smoothFlatOnDiagonal n ⊆ smoothSet (Config n) ∧
      IsFunctionSubspace (smoothFlatOnDiagonal n))
end YangMills.Construction.ConfigSpace
end
