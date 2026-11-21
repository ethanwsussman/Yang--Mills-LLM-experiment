import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.Ellipses
def IsJoukowskiRadius (z : ℂ) (r : ℝ) : Prop :=
  r ∈ Set.Ici (1 : ℝ) ∧ r + r⁻¹ = ‖z + 1‖ + ‖z - 1‖
def joukowskiRadius (z : ℂ) : ℝ := Classical.epsilon (IsJoukowskiRadius z)
def focalEllipse (ς : ℝ) (_hς : 1 < ς) : Set ℂ := {z | joukowskiRadius z < ς}
def polyEllipseDomain (n : ℕ) (_hn : 1 ≤ n) (ς : ℝ) (_hς : 1 < ς) : Set (Fin n → ℂ) :=
  {z | ∏ j : Fin n, joukowskiRadius (z j) < ς}
end YangMills.Construction.Ellipses
