import YangMills.Construction.SummableBoundsOfTheFlow.HaarTermIsBounded
import Mathlib
set_option autoImplicit false
noncomputable section
open YangMills.Construction.BlockAverages YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction.Estimates
namespace HaarLogRatio
theorem sinc_bounds_of_le_one {u : ℝ} (h0 : 0 ≤ u) (h1 : u ≤ 1) :
    3 / 4 ≤ Real.sinc u ∧ Real.sinc u ≤ 1 := by
  rcases h0.eq_or_lt with rfl | hpos
  · simp
    norm_num
  · rw [Real.sinc_of_ne_zero hpos.ne']
    have hs := Real.sin_gt_sub_cube hpos
    have hl := Real.sin_le hpos.le
    refine ⟨?_, ?_⟩
    · rw [le_div_iff₀ hpos]
      nlinarith [mul_nonneg h0 (mul_nonneg h0 h0), mul_le_mul h1 h1 h0 zero_le_one]
    · rw [div_le_one hpos]
      exact hl
end HaarLogRatio
open HaarLogRatio in
theorem haarLogRatio_bound : haarLogRatioBoundStatement := by
  intro w hw
  obtain ⟨h1, h2⟩ := sinc_bounds_of_le_one (norm_nonneg w) hw
  have hu : ‖w‖ < Real.pi := lt_of_le_of_lt hw (by linarith [Real.pi_gt_three])
  have e : haarRadialDensity ‖w‖ / haarRadialDensity 0 = Real.sinc ‖w‖ ^ 2 := by
    simp only [haarRadialDensity]
    rw [if_pos hu, if_pos Real.pi_pos]
    simp only [Real.sinc_zero]
    field_simp
  unfold haarLogRatio
  rw [e]
  have h3 : (9 / 16 : ℝ) ≤ Real.sinc ‖w‖ ^ 2 := by nlinarith
  have h4 : Real.sinc ‖w‖ ^ 2 ≤ 1 := by nlinarith
  have hpos : 0 < Real.sinc ‖w‖ ^ 2 := by linarith
  have hlog0 : Real.log (Real.sinc ‖w‖ ^ 2) ≤ 0 := Real.log_nonpos hpos.le h4
  rw [abs_of_nonpos hlog0]
  have h5 : -1 ≤ Real.log (Real.sinc ‖w‖ ^ 2) := by
    rw [Real.le_log_iff_exp_le hpos]
    have : Real.exp (-1) ≤ 9 / 16 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
      have := Real.add_one_le_exp (1 : ℝ)
      norm_num at this ⊢
      linarith
    linarith
  linarith
end YangMills.Construction.Estimates
end
