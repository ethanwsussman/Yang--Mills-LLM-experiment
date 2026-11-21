import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Lattice
def admissibleCellSidePowers (L n : ℕ) (R : ℝ) : Set ℝ :=
  {x | (∃ k : ℤ, x = (L : ℝ) ^ k) ∧ 8 * (n : ℝ) * (R + 1) ≤ x}
def cellSideLength (L n : ℕ) (R : ℝ) : ℝ := sInf (admissibleCellSidePowers L n R)
end YangMills.Construction.Lattice
end
