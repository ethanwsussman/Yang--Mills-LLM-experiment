import YangMills.Construction.ClusterExpansionOfAStep.GroupGapIsSmoothForm
import YangMills.Construction.ColdStepAtMirrorFrames.GroupGapIsSmoothProof
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory intervalIntegral
namespace YangMills.Construction.ColdStepAtMirrorFrames
namespace HaarGapSmooth
def laplaceMoment (j : ℕ) (s : ℝ) : ℝ :=
  ∫ v in (0 : ℝ)..2, v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v
theorem haarRealPartDensity_nonneg (v : ℝ) : 0 ≤ haarRealPartDensity v := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.LogJacobianSlope.haarRealPartDensity_nonneg <;> assumption
theorem haarRealPartDensity_pos {v : ℝ} (hv₀ : 0 < v) (hv₂ : v < 2) : 0 < haarRealPartDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HaarGap.haarRealPartDensity_pos <;> assumption
theorem haarRealPartDensity_le_two {v : ℝ} (hv₂ : v ≤ 2) (hv₀ : 0 ≤ v) : haarRealPartDensity v ≤ 2 := by
  unfold haarRealPartDensity
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hsq : Real.sqrt (2 * v - v ^ 2) ≤ 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by nlinarith⟩
  have hq : 2 / Real.pi ≤ 1 := by
    rw [div_le_one (by linarith)]
    linarith
  have hq₀ : 0 ≤ 2 / Real.pi := by positivity
  nlinarith
theorem continuous_laplaceMoment_integrand (j : ℕ) (s : ℝ) :
    Continuous fun v : ℝ => v ^ j * Real.exp (-(s * v)) * haarRealPartDensity v := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.HaarGap.momentIntegrand_continuous <;> assumption
theorem laplaceMoment_zero_pos (s : ℝ) : 0 < laplaceMoment 0 s := by
  unfold laplaceMoment
  apply intervalIntegral.intervalIntegral_pos_of_pos_on
  · exact (continuous_laplaceMoment_integrand 0 s).intervalIntegrable _ _
  · intro v hv
    have := haarRealPartDensity_pos hv.1 hv.2
    have := Real.exp_pos (-(s * v))
    simp only [pow_zero, one_mul]
    positivity
  · norm_num
theorem hasDerivAt_laplaceMoment (j : ℕ) (s : ℝ) :
    HasDerivAt (laplaceMoment j) (-(laplaceMoment (j + 1) s)) s := by
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := volume) (a := (0 : ℝ)) (b := 2) (s := Metric.ball s 1)
    (F := fun (x v : ℝ) => v ^ j * Real.exp (-(x * v)) * haarRealPartDensity v)
    (F' := fun (x v : ℝ) => -(v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v))
    (x₀ := s) (bound := fun _ => 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2)
    (Metric.ball_mem_nhds s one_pos)
    (Filter.Eventually.of_forall fun x =>
      ((continuous_laplaceMoment_integrand j x).aestronglyMeasurable).restrict)
    ((continuous_laplaceMoment_integrand j s).intervalIntegrable _ _)
    (((continuous_laplaceMoment_integrand (j + 1) s).neg).aestronglyMeasurable.restrict)
    ?_ (by exact intervalIntegrable_const) ?_
  · have hderiv := key.2
    rw [intervalIntegral.integral_neg] at hderiv
    exact hderiv
  · refine Filter.Eventually.of_forall fun v hv x hx => ?_
    rw [Set.uIoc_of_le (by norm_num)] at hv
    have hv₀ : 0 ≤ v := hv.1.le
    have hv₂ : v ≤ 2 := hv.2
    have hx' : |x| ≤ |s| + 1 := by
      have hxs : |x - s| < 1 := by simpa [Real.dist_eq] using hx
      have htri := abs_sub_abs_le_abs_sub x s
      linarith
    have hexp : Real.exp (-(x * v)) ≤ Real.exp (2 * (|s| + 1)) := by
      apply Real.exp_le_exp.mpr
      have hneg : -(x * v) ≤ |x| * v := by
        have := neg_abs_le x
        nlinarith
      nlinarith [abs_nonneg x]
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg (by
      have := haarRealPartDensity_nonneg v
      positivity)]
    have hpow : v ^ (j + 1) ≤ 2 ^ (j + 1) := pow_le_pow_left₀ hv₀ hv₂ _
    have hdens := haarRealPartDensity_le_two hv₂ hv₀
    have hdens₀ := haarRealPartDensity_nonneg v
    exact show v ^ (j + 1) * Real.exp (-(x * v)) * haarRealPartDensity v
        ≤ 2 ^ (j + 1) * Real.exp (2 * (|s| + 1)) * 2 from by gcongr
  · refine Filter.Eventually.of_forall fun v _ x _ => ?_
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (-(y * v))) (Real.exp (-(x * v)) * (-v)) x := by
      have : HasDerivAt (fun y : ℝ => -(y * v)) (-v) x :=
        HasDerivAt.congr_deriv ((hasDerivAt_id x).mul_const v).neg (by ring)
      exact this.exp
    have hprod := (hexp.const_mul (v ^ j)).mul_const (haarRealPartDensity v)
    refine HasDerivAt.congr_deriv hprod ?_
    ring
theorem contDiff_laplaceMoment (k : ℕ) : ∀ j, ContDiff ℝ k (laplaceMoment j) := by
  induction k with
  | zero =>
    intro j
    exact contDiff_zero.mpr
      (continuous_iff_continuousAt.mpr fun s => (hasDerivAt_laplaceMoment j s).continuousAt)
  | succ k ih =>
    intro j
    have hd : deriv (laplaceMoment j) = fun s => -(laplaceMoment (j + 1) s) :=
      funext fun s => (hasDerivAt_laplaceMoment j s).deriv
    have hk : ContDiff ℝ (((k : ℕ) : WithTop ℕ∞) + 1) (laplaceMoment j) := by
      rw [contDiff_succ_iff_deriv]
      refine ⟨fun s => (hasDerivAt_laplaceMoment j s).differentiableAt, by simp, ?_⟩
      rw [hd]
      exact (ih (j + 1)).neg
    exact_mod_cast hk
theorem haarGap_eq_neg_log (s : ℝ) : haarGap s = - Real.log (laplaceMoment 0 s) := by
  have e : laplaceMoment 0 s = haarLaplace s := by
    unfold laplaceMoment haarLaplace
    simp
  unfold haarGap haarCharacterMean
  rw [e]
  have hm : 0 < haarLaplace s := by
    rw [← e]
    exact laplaceMoment_zero_pos s
  rw [Real.log_mul (Real.exp_pos s).ne' hm.ne', Real.log_exp]
  ring
end HaarGapSmooth
open HaarGapSmooth in
theorem haarGapSmoothStatement_holds : HaarGapSmoothStatement := by
  have h : haarGap = fun s => - Real.log (laplaceMoment 0 s) := funext haarGap_eq_neg_log
  unfold HaarGapSmoothStatement
  rw [h]
  exact ((contDiff_laplaceMoment 3 0).log fun s => (laplaceMoment_zero_pos s).ne').neg
end YangMills.Construction.ColdStepAtMirrorFrames
end
