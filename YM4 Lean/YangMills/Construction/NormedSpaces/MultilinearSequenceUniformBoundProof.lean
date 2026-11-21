import YangMills.Construction.NormedSpaces.MultilinearSequenceUniformBound
import YangMills.Construction.NormedSpaces.UniformBoundMultilinearForms
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.NormedSpaces
open BanachSteinhaus
theorem multilinearSequenceUniformBound_of_principle
    (hPrinciple : MultilinearUniformBound.uniformBoundednessPrinciple) :
    MultilinearSequenceUniformBound := by
  intro k X _ _ _ B hB hpt
  have hpolyball : ∀ n, BddAbove (formValuesOnUnitPolyball (B n)) := by
    intro n
    obtain ⟨c, hc⟩ := hB n
    refine ⟨|c|, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    have hprod_le : ∏ i, ‖x i‖ ≤ 1 :=
      Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => hx i)
    have hprod_nonneg : 0 ≤ ∏ i, ‖x i‖ := Finset.prod_nonneg (fun i _ => norm_nonneg _)
    calc |B n x| ≤ c * ∏ i, ‖x i‖ := hc x
      _ ≤ |c| * ∏ i, ‖x i‖ := mul_le_mul_of_nonneg_right (le_abs_self c) hprod_nonneg
      _ ≤ |c| * 1 := mul_le_mul_of_nonneg_left hprod_le (abs_nonneg c)
      _ = |c| := mul_one _
  obtain ⟨⟨C, hC⟩, -, -⟩ := hPrinciple ℕ+ k (Nat.succ_le_of_lt k.pos) X B hpolyball hpt
  exact ⟨C, hC⟩
end YangMills.Construction.NormedSpaces
