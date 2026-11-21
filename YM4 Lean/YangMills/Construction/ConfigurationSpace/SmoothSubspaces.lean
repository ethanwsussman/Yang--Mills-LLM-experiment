import YangMills.Construction.Continuum.ConfigurationSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
open scoped ENNReal
def IsLinearFunctionSet {X : Type*} (S : Set (X → ℂ)) : Prop :=
  (0 : X → ℂ) ∈ S ∧ (∀ φ ∈ S, ∀ ψ ∈ S, φ + ψ ∈ S) ∧ ∀ (c : ℂ), ∀ φ ∈ S, c • φ ∈ S
def weightedDerivSup {n : ℕ} (k : ℕ) (α : MultiIdx (CoordIndex n))
    (φ : Config n → ℂ) : ℝ≥0∞ :=
  ⨆ x, ENNReal.ofReal ((1 + configNorm x) ^ k * ‖configMultiDeriv α φ x‖)
def rapidDecaySet (n : ℕ) : Set (Config n → ℂ) :=
  {φ | φ ∈ smoothSet (Config n) ∧
    ∀ (k : ℕ) (α : MultiIdx (CoordIndex n)), weightedDerivSup k α φ < ⊤}
def flatOnDiagonalSet (n : ℕ) : Set (Config n → ℂ) :=
  {φ | φ ∈ smoothSet (Config n) ∧
    ∀ x ∈ fatDiagonal n, ∀ α : MultiIdx (CoordIndex n), configMultiDeriv α φ x = 0}
def SmoothSubspaces : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    IsLinearFunctionSet (smoothSet (Config n)) ∧
    (rapidDecaySet n ⊆ smoothSet (Config n) ∧
      IsLinearFunctionSet (rapidDecaySet n)) ∧
    (flatOnDiagonalSet n ⊆ smoothSet (Config n) ∧
      IsLinearFunctionSet (flatOnDiagonalSet n))
end YangMills.Construction.ConfigurationSpace
end
