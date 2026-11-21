import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MatrixDeterminants
def LogDetOneAddBound : Prop :=
  ∀ (α : Type) [Fintype α] [DecidableEq α] (A : Matrix α α ℝ) (s : ℝ), 0 ≤ s → s ≤ 1 / 8 →
    (∑ i, ∑ j, A i j ^ 2) ≤ s ^ 2 →
    (1 + A).det ≠ 0 ∧ |Real.log (abs (1 + A).det)| ≤ 3 * Real.sqrt (Fintype.card α) * s
end YangMills.Construction.MatrixDeterminants
end
