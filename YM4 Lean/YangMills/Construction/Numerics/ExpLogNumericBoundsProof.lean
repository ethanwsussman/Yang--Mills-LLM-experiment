import YangMills.Construction.Numerics.ExpLogNumericBounds
import Mathlib
open Real
namespace YangMills.Construction.Numerics
private theorem exp_lt_of_quartic_taylor_bound {x y : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x ≤ 1)
    (hy : 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 + x ^ 5 * 6 / 600 < y) : exp x < y := by
  refine lt_of_le_of_lt (Real.exp_bound' hx₀ hx₁ (n := 5) (by norm_num)) (lt_of_le_of_lt (le_of_eq ?_) hy)
  simp [Finset.sum_range_succ, Nat.factorial]
  ring
private theorem quartic_taylor_le_exp {x : ℝ} (hx₀ : 0 ≤ x) :
    1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24 ≤ exp x := by
  refine le_trans (le_of_eq ?_) (Real.sum_le_exp_of_nonneg hx₀ 5)
  simp [Finset.sum_range_succ, Nat.factorial]
theorem expLogNumericBounds_holds : ExpLogNumericBounds := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · exact exp_lt_of_quartic_taylor_bound (by norm_num) (by norm_num) (by norm_num)
  · rw [Real.log_lt_iff_lt_exp (by norm_num)]
    refine lt_of_lt_of_le ?_ (quartic_taylor_le_exp (x := 0.1178) (by norm_num))
    norm_num
  · have hlog := Real.log_two_gt_d9
    norm_num at hlog ⊢
    linarith
  · have hten : Real.log 10 < 3 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      refine lt_of_lt_of_le ?_ (quartic_taylor_le_exp (x := 3) (by norm_num))
      norm_num
    linarith [Real.pi_gt_three]
end YangMills.Construction.Numerics
