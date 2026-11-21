import YangMills.Construction.ClusterExpansionOfAStep.SlopeOfTheLogOfASettingProof
import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmooth
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory intervalIntegral
namespace YangMills.Construction.ColdStepAtMirrorFrames.HaarGap
def haarMoment (j : ℕ) (s : ℝ) : ℝ := ∫ v in (0 : ℝ)..2, v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v
theorem haarRealPartDensity_continuous : Continuous haarRealPartDensity := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.continuous_haarRealPartDensity <;> assumption
theorem haarRealPartDensity_nonneg (v : ℝ) : 0 ≤ haarRealPartDensity v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.haarRealPartDensity_nonneg <;> assumption
theorem haarRealPartDensity_pos {v : ℝ} (hv0 : 0 < v) (hv2 : v < 2) : 0 < haarRealPartDensity v := by
  unfold haarRealPartDensity
  have : 0 < 2 * v - v ^ 2 := by nlinarith
  have := Real.sqrt_pos.mpr this
  positivity
theorem haarRealPartDensity_le_two {v : ℝ} (_hv0 : 0 ≤ v) (hv2 : v ≤ 2) : haarRealPartDensity v ≤ 2 := by
  unfold haarRealPartDensity
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hs : Real.sqrt (2 * v - v ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have h1 : 2 / Real.pi ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have h3 : 0 ≤ 2 / Real.pi := by positivity
  nlinarith
theorem momentIntegrand_continuous (j : ℕ) (s : ℝ) :
    Continuous fun v : ℝ => v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v := by
  have := haarRealPartDensity_continuous
  fun_prop
theorem haarMoment_zero_pos (s : ℝ) : 0 < haarMoment 0 s := by
  unfold haarMoment
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (momentIntegrand_continuous 0 s).intervalIntegrable _ _
  · intro v hv
    have := haarRealPartDensity_pos hv.1 hv.2
    have := Real.exp_pos (-(s * v))
    simp only [pow_zero, one_mul]
    positivity
  · norm_num
theorem haarMoment_zero_eq (s : ℝ) : haarMoment 0 s = haarLaplace s := by
  unfold haarMoment haarLaplace
  simp
theorem hasDerivAt_haarMoment (j : ℕ) (s : ℝ) : HasDerivAt (haarMoment j) (-(haarMoment (j + 1) s)) s := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2) (s := Metric.ball s 1)
    (F := fun (x v : ℝ) => v ^ j * Real.exp (-(x * v)) * haarRealPartDensity v)
    (F' := fun (x v : ℝ) => -(v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v))
    (x₀ := s) (bound := fun _ => 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((momentIntegrand_continuous j x).aestronglyMeasurable).restrict)
    ((momentIntegrand_continuous j s).intervalIntegrable _ _)
    (((momentIntegrand_continuous (j + 1) s).neg).aestronglyMeasurable.restrict)
    ?_ (by exact intervalIntegrable_const) ?_
  · have h := key.2
    rw [intervalIntegral.integral_neg] at h
    exact h
  · refine Filter.Eventually.of_forall fun v hv x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hv
    have hv0 : 0 ≤ v := hv.1.le
    have hv2 : v ≤ 2 := hv.2
    have hx' : |x| ≤ |s| + 1 := by
      have h1 : |x - s| < 1 := by simpa [Real.dist_eq] using hx
      have h2 := abs_sub_abs_le_abs_sub x s
      linarith
    have he : Real.exp (-(x * v)) ≤ Real.exp (2 * (|s| + 1)) := by
      apply Real.exp_le_exp.mpr
      have h3 : -(x * v) ≤ |x| * v := by
        have := neg_abs_le x
        nlinarith
      nlinarith [abs_nonneg x]
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by
      have := haarRealPartDensity_nonneg v
      positivity)]
    have h1 : v ^ (j + 1) ≤ 2 ^ (j + 1) := pow_le_pow_left₀ hv0 hv2 _
    have h2 := haarRealPartDensity_le_two hv0 hv2
    have h3 := haarRealPartDensity_nonneg v
    exact show v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v
        ≤ 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2 from by gcongr
  · refine Filter.Eventually.of_forall fun v _ x _ => ?_
    have h1 : HasDerivAt (fun y : ℝ => Real.exp (-(y * v))) (Real.exp (-(x * v)) * (-v)) x := by
      have : HasDerivAt (fun y : ℝ => -(y * v)) (-v) x :=
        HasDerivAt.congr_deriv ((hasDerivAt_id x).mul_const v).neg (by ring)
      exact this.exp
    have h2 := (h1.const_mul (v ^ j)).mul_const (haarRealPartDensity v)
    refine HasDerivAt.congr_deriv h2 ?_
    ring
theorem haarGap_eq_neg_log (s : ℝ) : haarGap s = - Real.log (haarMoment 0 s) := by
  unfold haarGap haarCharacterMean
  rw [haarMoment_zero_eq]
  have hm : 0 < haarLaplace s := by
    rw [← haarMoment_zero_eq]
    exact haarMoment_zero_pos s
  rw [Real.log_mul (Real.exp_pos s).ne' hm.ne', Real.log_exp]
  ring
theorem haarMoment_contDiff (n : ℕ) : ∀ j, ContDiff ℝ n (haarMoment j) := by
  induction n with
  | zero =>
    intro j
    rw [Nat.cast_zero, contDiff_zero]
    exact continuous_iff_continuousAt.2 fun s => (hasDerivAt_haarMoment j s).continuousAt
  | succ n ih =>
    intro j
    have hd : deriv (haarMoment j) = fun s => -(haarMoment (j + 1) s) :=
      funext fun s => (hasDerivAt_haarMoment j s).deriv
    have : ContDiff ℝ ((n : WithTop ℕ∞) + 1) (haarMoment j) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun s => (hasDerivAt_haarMoment j s).differentiableAt, by simp, ?_⟩
      rw [hd]
      exact (ih (j + 1)).neg
    exact_mod_cast this
theorem haarGap_contDiff : HaarGapContDiff := by
  have h : haarGap = fun s => - Real.log (haarMoment 0 s) := funext haarGap_eq_neg_log
  unfold HaarGapContDiff
  rw [h]
  exact ((haarMoment_contDiff 3 0).log fun s => (haarMoment_zero_pos s).ne').neg
end YangMills.Construction.ColdStepAtMirrorFrames.HaarGap
end
