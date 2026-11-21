import YangMills.Construction.InequalityOnMirroredCopies.SizeAtASmallRadius
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectedCopies.CopySizeSmallRadius
private theorem mul_le_mul_max_add_pow_twenty (b u : ℝ) (hb : 0 ≤ b) (hu : 0 ≤ u) :
    b * u ≤ b * max 1 b + u ^ 20 := by
  have hm : 0 ≤ b * max 1 b := mul_nonneg hb (le_trans zero_le_one (le_max_left 1 b))
  rcases le_total u (max 1 b) with h | h
  · have h1 : b * u ≤ b * max 1 b := mul_le_mul_of_nonneg_left h hb
    have h2 : 0 ≤ u ^ 20 := pow_nonneg hu 20
    linarith
  · have h1 : (1 : ℝ) ≤ u := le_trans (le_max_left 1 b) h
    have h2 : b ≤ u := le_trans (le_max_right 1 b) h
    have h3 : u ^ 2 ≤ u ^ 20 := pow_le_pow_right₀ h1 (by norm_num)
    have h4 : b * u ≤ u ^ 2 := by nlinarith
    linarith
theorem holds : CopySizeSmallRadius.Statement := by
  intro A b hA hb
  refine ⟨A * Real.exp (b + b * max 1 b), mul_nonneg hA (Real.exp_pos _).le,
    fun l ϱ hl hl1 hϱ hϱ1 => ?_⟩
  have hinv : 1 ≤ 1 / ϱ := by
    rw [le_div_iff₀ hϱ]
    linarith
  have hlog : 0 ≤ Real.log (1 / ϱ) := Real.log_nonneg hinv
  have ht : TorusBound.logPos (1 / ϱ) = Real.log (1 / ϱ) := by
    unfold TorusBound.logPos
    exact max_eq_left hlog
  have hu : 0 ≤ Real.log (1 / ϱ) ^ (1 / 20 : ℝ) := Real.rpow_nonneg hlog _
  have hpow : (Real.log (1 / ϱ) ^ (1 / 20 : ℝ)) ^ 20 = Real.log (1 / ϱ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    norm_num
  have hlin := mul_le_mul_max_add_pow_twenty b (Real.log (1 / ϱ) ^ (1 / 20 : ℝ)) hb hu
  rw [hpow] at hlin
  have hl4 : l ^ 4 ≤ 1 := pow_le_one₀ hl.le hl1
  have hbl : b * l ^ 4 ≤ b := by nlinarith
  have hexp : Real.exp (b * l ^ 4 + b * Real.log (1 / ϱ) ^ (1 / 20 : ℝ)) ≤
      Real.exp (b + b * max 1 b) * (1 / ϱ) := by
    have h1 : Real.exp (b + b * max 1 b) * (1 / ϱ) =
        Real.exp (b + b * max 1 b + Real.log (1 / ϱ)) := by
      rw [Real.exp_add _ (Real.log (1 / ϱ)), Real.exp_log (by positivity)]
    rw [h1]
    exact Real.exp_le_exp.mpr (by linarith)
  unfold copySize
  rw [ht]
  calc A * Real.exp (b * l ^ 4 + b * Real.log (1 / ϱ) ^ (1 / 20 : ℝ))
      ≤ A * (Real.exp (b + b * max 1 b) * (1 / ϱ)) := mul_le_mul_of_nonneg_left hexp hA
    _ = A * Real.exp (b + b * max 1 b) / ϱ := by ring
end YangMills.Construction.ReflectedCopies.CopySizeSmallRadius
end
