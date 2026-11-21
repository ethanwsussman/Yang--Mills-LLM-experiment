import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASettingProof
import YangMills.Construction.SummableBoundsOfTheFlow.GroupGapHasItsTail
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace YangMills.Construction.ScaledVariables
open YangMills.Construction.ColdStepAtMirrorFrames
private theorem sqrt_mul_sqrt_two_sub {w : ℝ} (hw : 0 < w) :
    Real.sqrt w * Real.sqrt (2 - w) = Real.sqrt (2 * w - w ^ 2) := by
  rw [← Real.sqrt_mul hw.le]
  congr 1
  ring
private theorem haarLaplace_eq_integral_Ioi (s : ℝ) :
    haarLaplace s = 2 / Real.pi * ∫ w in Ioi (0 : ℝ), Real.exp (-(s * w)) * (Real.sqrt w * Real.sqrt (2 - w)) := by
  unfold haarLaplace haarRealPartDensity
  have hconst : ∫ v in (0 : ℝ)..2, Real.exp (-(s * v)) * (2 / Real.pi * Real.sqrt (2 * v - v ^ 2)) =
      2 / Real.pi * ∫ v in (0 : ℝ)..2, Real.exp (-(s * v)) * Real.sqrt (2 * v - v ^ 2) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1
    funext v
    ring
  rw [hconst]
  congr 1
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 2)]
  have hrestrict : ∫ w in Ioi (0 : ℝ), Real.exp (-(s * w)) * (Real.sqrt w * Real.sqrt (2 - w)) =
      ∫ w in Ioc (0 : ℝ) 2, Real.exp (-(s * w)) * (Real.sqrt w * Real.sqrt (2 - w)) := by
    rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioc]
    congr 1
    funext w
    by_cases hpos : 0 < w
    · by_cases hle : w ≤ 2
      · simp [indicator, hpos, hle]
      · have hnp : 2 - w ≤ 0 := by linarith [not_le.mp hle]
        simp [indicator, hpos, hle, Real.sqrt_eq_zero_of_nonpos hnp]
    · simp [indicator, hpos]
  rw [hrestrict]
  refine setIntegral_congr_fun measurableSet_Ioc ?_
  intro w hw
  simp only
  rw [sqrt_mul_sqrt_two_sub hw.1]
private theorem haarLaplace_pos (s : ℝ) : 0 < haarLaplace s := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.haarLaplace_pos <;> assumption
theorem haarGapLogTail_holds : HaarGapLogTail := by
  intro s hs
  have hZ := haarLaplace_pos s
  have htail : (2 / Real.pi * ∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.sqrt v * Real.sqrt (2 - 1 / s * v)) =
      s ^ ((3 : ℝ) / 2) * haarLaplace s := by
    have hsub := integral_comp_mul_left_Ioi
      (fun v : ℝ => Real.exp (-v) * Real.sqrt v * Real.sqrt (2 - 1 / s * v)) 0 hs
    rw [mul_zero] at hsub
    have hscale : (∫ v in Ioi (0 : ℝ), Real.exp (-v) * Real.sqrt v * Real.sqrt (2 - 1 / s * v)) =
        s * ∫ w in Ioi (0 : ℝ), Real.exp (-(s * w)) * Real.sqrt (s * w) * Real.sqrt (2 - 1 / s * (s * w)) := by
      rw [hsub, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    have hroot : (∫ w in Ioi (0 : ℝ), Real.exp (-(s * w)) * Real.sqrt (s * w) * Real.sqrt (2 - 1 / s * (s * w))) =
        Real.sqrt s * ∫ w in Ioi (0 : ℝ), Real.exp (-(s * w)) * (Real.sqrt w * Real.sqrt (2 - w)) := by
      rw [← integral_const_mul]
      refine setIntegral_congr_fun measurableSet_Ioi ?_
      intro w _
      simp only
      have hcancel : 1 / s * (s * w) = w := by field_simp
      rw [hcancel, Real.sqrt_mul hs.le]
      ring
    have hpow : s ^ ((3 : ℝ) / 2) = s * Real.sqrt s := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_one_add' hs.le (by norm_num)]
      norm_num
    rw [hscale, hroot, haarLaplace_eq_integral_Ioi, hpow]
    ring
  unfold haarGapTail haarGap haarCharacterMean
  rw [htail, Real.log_mul (Real.exp_pos s).ne' hZ.ne', Real.log_exp,
    Real.log_mul (Real.rpow_pos_of_pos hs _).ne' hZ.ne', Real.log_rpow hs]
  ring
end YangMills.Construction.ScaledVariables
end
