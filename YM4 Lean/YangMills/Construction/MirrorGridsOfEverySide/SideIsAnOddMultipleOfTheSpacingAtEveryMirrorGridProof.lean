import YangMills.Construction.MirrorGridsOfEverySide.SideIsAnOddMultipleOfTheSpacingAtEveryMirrorGrid
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MirrorGridsAllSides
theorem cellSideOddMultipleEveryGrid_holds : CellSideOddMultipleEveryGrid := by
  intro D Γ hΓ
  unfold CellSideOddMultiple
  have ha : 0 < D.mesh := D.mesh_pos
  have hL : (0 : ℝ) < (D.L : ℝ) ^ 2 := pow_pos (by linarith [D.one_lt_factor]) 2
  have hratio : Γ.cellSide / D.mesh = (Γ.cellRatio : ℝ) := by
    rw [Γ.cellSide_eq]
    field_simp
  have hodd : Odd (D.L : ℤ) := (Int.odd_coe_nat _).2 D.isAdmissible.1
  refine ⟨⟨Γ.cellRatio, ?_, hratio⟩, ?_⟩
  · exact hodd.pow
  · have hle := (le_div_iff₀ hL).1 hΓ.2
    rw [le_div_iff₀ ha]
    linarith
end YangMills.Construction.MirrorGridsAllSides
end
