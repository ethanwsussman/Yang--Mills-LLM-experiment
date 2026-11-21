import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.SeparatedSequences
structure IsPieceCutoff (χ : ℝ → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  antitone : Antitone χ
  eq_one_of_nonpos : ∀ x, x ≤ 0 → χ x = 1
  eq_zero_of_one_le : ∀ x, 1 ≤ x → χ x = 0
theorem exists_isPieceCutoff : ∃ χ : ℝ → ℝ, IsPieceCutoff χ :=
  ⟨fun x => 1 - Real.smoothTransition x,
    contDiff_const.sub Real.smoothTransition.contDiff,
    fun _ _ hxy => sub_le_sub_left (Real.smoothTransition.monotone hxy) 1,
    fun x hx => by simp [Real.smoothTransition.zero_of_nonpos hx],
    fun x hx => by simp [Real.smoothTransition.one_of_one_le hx]⟩
def pieceCutoff : ℝ → ℝ := Classical.choose exists_isPieceCutoff
end YangMills.Construction.SeparatedSequences
end
