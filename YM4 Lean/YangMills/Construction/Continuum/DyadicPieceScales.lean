import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.PieceScales
def IsSideConstant (c : ℝ) : Prop := 0 < c ∧ c ≤ 1 / 6
theorem exists_isSideConstant : ∃ c, IsSideConstant c :=
  ⟨1 / 6, by norm_num, le_rfl⟩
noncomputable def sideConstant : ℝ := Classical.epsilon IsSideConstant
theorem isSideConstant_sideConstant : IsSideConstant sideConstant :=
  Classical.epsilon_spec exists_isSideConstant
noncomputable def dyadicScale (j : ℕ) : ℝ := (2 : ℝ) ^ (-(j : ℤ))
noncomputable def pieceSide (j : ℕ) : ℝ := sideConstant * dyadicScale j
end YangMills.Construction.PieceScales
