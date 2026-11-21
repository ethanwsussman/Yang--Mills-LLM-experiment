import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.Matrices.HaarExpChartDensityProof
import YangMills.Construction.RunningCouplingSlope.HaarDensityAtTheLeastFieldHasKernelsProof
import YangMills.Construction.ColdStepAtMirrorFrames.HaarExcessNearZero
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open YangMills.Construction.BlockAverages Filter
namespace YangMills.Construction.ColdStepAtMirrorFrames.HaarLogRatio
abbrev smoothTop : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem natCast_le_smoothTop (j : ℕ) : (j : WithTop ℕ∞) ≤ smoothTop := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
def sincCoeff (n : ℕ) : ℝ := (-1) ^ n / ((2 * n + 1).factorial : ℝ)
def sincOfSq (s : ℝ) : ℝ := FormalMultilinearSeries.ofScalarsSum (E := ℝ) sincCoeff s
theorem contDiff_sincOfSq : ContDiff ℝ smoothTop sincOfSq := by apply _root_.YangMills.DeltaSharedProofs.p502125 <;> assumption
theorem sincOfSq_sq (u : ℝ) : sincOfSq (u ^ 2) = Real.sinc u := by apply _root_.YangMills.DeltaSharedProofs.p500885 <;> assumption
def sincNorm (v : imaginaryQuaternions) : ℝ := sincOfSq (‖v‖ ^ 2)
theorem sincNorm_eq (v : imaginaryQuaternions) : sincNorm v = Real.sinc ‖v‖ := sincOfSq_sq _
theorem contDiff_sincNorm : ContDiff ℝ smoothTop sincNorm :=
  contDiff_sincOfSq.comp (contDiff_norm_sq ℝ)
theorem sincNorm_pos {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) : 0 < sincNorm v := by apply _root_.YangMills.DeltaSharedProofs.p500794 <;> assumption
def logSincNormSq (v : imaginaryQuaternions) : ℝ := Real.log (sincNorm v ^ 2)
theorem haarLogRatio_eq {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) :
    haarLogRatio v = logSincNormSq v := by apply _root_.YangMills.DeltaSharedProofs.p501611 <;> assumption
theorem contDiffAt_logSincNormSq {v : imaginaryQuaternions} (hv : ‖v‖ < Real.pi) :
    ContDiffAt ℝ smoothTop logSincNormSq v := by
  have h1 : ContDiffAt ℝ smoothTop (fun v => sincNorm v ^ 2) v :=
    (contDiff_sincNorm.pow 2).contDiffAt
  have h2 : sincNorm v ^ 2 ≠ 0 := pow_ne_zero _ (sincNorm_pos hv).ne'
  exact h1.log h2
theorem exists_bound_iteratedFDeriv (j : ℕ) :
    ∃ C : ℝ, ∀ v : imaginaryQuaternions, ‖v‖ ≤ 1 → ‖iteratedFDeriv ℝ j logSincNormSq v‖ ≤ C := by
  have : ProperSpace imaginaryQuaternions := FiniteDimensional.proper_real imaginaryQuaternions
  have hK : IsCompact (Metric.closedBall (0 : imaginaryQuaternions) 1) := isCompact_closedBall _ _
  have hc : ContinuousOn (fun v : imaginaryQuaternions => ‖iteratedFDeriv ℝ j logSincNormSq v‖)
      (Metric.closedBall (0 : imaginaryQuaternions) 1) := by
    intro v hv
    have hv' : ‖v‖ < Real.pi := by
      have : ‖v‖ ≤ 1 := by simpa using hv
      linarith [Real.pi_gt_three]
    have h1 : ContDiffAt ℝ 0 (iteratedFDeriv ℝ j logSincNormSq) v :=
      (contDiffAt_logSincNormSq hv').iteratedFDeriv_right (m := 0) (i := j) (by
        simp only [zero_add]
        exact natCast_le_smoothTop j)
    have h5 : ContinuousAt (fun v : imaginaryQuaternions => ‖iteratedFDeriv ℝ j logSincNormSq v‖) v :=
      ContinuousAt.comp (f := iteratedFDeriv ℝ j logSincNormSq)
        (g := fun A => ‖A‖)
        (continuous_norm
          (E := ContinuousMultilinearMap ℝ (fun _ : Fin j => imaginaryQuaternions) ℝ)).continuousAt
        h1.continuousAt
    exact h5.continuousWithinAt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc
  exact ⟨C, fun v hv => (le_abs_self _).trans (by simpa using hC v (by simpa using hv))⟩
theorem haarLogRatioNearZero_holds : HaarLogRatioNearZero := by
  obtain ⟨C1, h1⟩ := exists_bound_iteratedFDeriv 1
  obtain ⟨C2, h2⟩ := exists_bound_iteratedFDeriv 2
  refine ⟨|C1| + |C2| + 1, by positivity, ?_⟩
  intro v hv
  have hv' : ‖v‖ < Real.pi := by linarith [Real.pi_gt_three]
  have hop : IsOpen {z : imaginaryQuaternions | ‖z‖ < Real.pi} :=
    isOpen_lt continuous_norm continuous_const
  have hev : haarLogRatio =ᶠ[𝓝 v] logSincNormSq := by
    filter_upwards [hop.mem_nhds hv'] with z hz using haarLogRatio_eq hz
  have hcd : ContDiffAt ℝ smoothTop logSincNormSq v := contDiffAt_logSincNormSq hv'
  have hc3 : ContDiffAt ℝ 3 logSincNormSq v := hcd.of_le (by exact_mod_cast natCast_le_smoothTop 3)
  have hf : fderiv ℝ haarLogRatio =ᶠ[𝓝 v] fderiv ℝ logSincNormSq :=
    Filter.EventuallyEq.fderiv (𝕜 := ℝ) hev
  have a1 := abs_nonneg C1
  have a2 := abs_nonneg C2
  refine ⟨hc3.congr_of_eventuallyEq hev, ?_, ?_⟩
  · intro e
    rw [hf.eq_of_nhds]
    have hb : ‖fderiv ℝ logSincNormSq v‖ ≤ |C1| + |C2| + 1 := by
      have := h1 v hv
      rw [norm_iteratedFDeriv_one] at this
      linarith [le_abs_self C1]
    calc |fderiv ℝ logSincNormSq v e| = ‖fderiv ℝ logSincNormSq v e‖ := (Real.norm_eq_abs _).symm
      _ ≤ ‖fderiv ℝ logSincNormSq v‖ * ‖e‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right hb (norm_nonneg _)
  · intro e e'
    have he : (fun z => fderiv ℝ haarLogRatio z e) =ᶠ[𝓝 v] fun z => fderiv ℝ logSincNormSq z e := by
      filter_upwards [hf] with z hz
      rw [hz]
    rw [he.fderiv_eq]
    have h2c : ContDiffAt ℝ 2 (fderiv ℝ logSincNormSq) v := hc3.fderiv_right (by norm_num)
    have hd : DifferentiableAt ℝ (fderiv ℝ logSincNormSq) v := h2c.differentiableAt (by norm_num)
    have hm : fderiv ℝ (fun z => fderiv ℝ logSincNormSq z e) v e' =
        iteratedFDeriv ℝ 2 logSincNormSq v ![e', e] := by
      rw [iteratedFDeriv_two_apply, (hd.hasFDerivAt.clm_apply (hasFDerivAt_const e v)).fderiv]
      simp
    rw [hm]
    have h3 := (iteratedFDeriv ℝ 2 logSincNormSq v).le_opNorm ![e', e]
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one] at h3
    have hb : ‖iteratedFDeriv ℝ 2 logSincNormSq v‖ ≤ |C1| + |C2| + 1 := by
      have := h2 v hv
      linarith [le_abs_self C2]
    have n1 := norm_nonneg e
    have n2 := norm_nonneg e'
    calc |iteratedFDeriv ℝ 2 logSincNormSq v ![e', e]| = ‖iteratedFDeriv ℝ 2 logSincNormSq v ![e', e]‖ :=
          (Real.norm_eq_abs _).symm
      _ ≤ ‖iteratedFDeriv ℝ 2 logSincNormSq v‖ * (‖e'‖ * ‖e‖) := h3
      _ ≤ (|C1| + |C2| + 1) * (‖e'‖ * ‖e‖) := mul_le_mul_of_nonneg_right hb (by positivity)
      _ = _ := by ring
end YangMills.Construction.ColdStepAtMirrorFrames.HaarLogRatio
end
