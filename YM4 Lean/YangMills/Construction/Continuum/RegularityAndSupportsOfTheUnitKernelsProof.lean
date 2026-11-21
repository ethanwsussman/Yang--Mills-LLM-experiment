import YangMills.Construction.Continuum.CutoffOfTheParametrix
import YangMills.Construction.Continuum.PlateauOfAFunctionOnTuples
import YangMills.Construction.Continuum.RegularityAndSupportsOfTheUnitKernels
import YangMills.Construction.Continuum.ThreeLaplaciansOfTheLogKernel
import Mathlib
set_option autoImplicit false
open scoped ContDiff Topology
noncomputable section
namespace YangMills.Construction
namespace Parametrix
namespace UnitKernelSupport
open TorusMetric TestFunctions Filter
def sumSq (x : Fin 4 → ℝ) : ℝ := ∑ μ, x μ ^ 2
theorem sumSq_nonneg (x : Fin 4 → ℝ) : 0 ≤ sumSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _
theorem euclidNormVec_sq (x : Fin 4 → ℝ) : euclidNormVec x ^ 2 = sumSq x :=
  Real.sq_sqrt (sumSq_nonneg x)
theorem euclidNormVec_nonneg (x : Fin 4 → ℝ) : 0 ≤ euclidNormVec x := Real.sqrt_nonneg _
theorem continuous_euclidNormVec : Continuous euclidNormVec := by apply _root_.YangMills.Construction.SeparatedTuples.continuous_euclidNormVec <;> assumption
theorem contDiff_sumSq : ContDiff ℝ ∞ sumSq :=
  ContDiff.sum fun μ _ => (contDiff_apply ℝ ℝ μ).pow 2
theorem eq_zero_of_sumSq_eq_zero {x : Fin 4 → ℝ} (h : sumSq x = 0) : x = 0 := by
  funext μ
  have := (Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _).1 h μ (Finset.mem_univ μ)
  simpa using this
theorem sq_apply_le_sumSq (x : Fin 4 → ℝ) (μ : Fin 4) : x μ ^ 2 ≤ sumSq x :=
  Finset.single_le_sum (f := fun ν => x ν ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ μ)
theorem abs_apply_le_euclidNormVec (x : Fin 4 → ℝ) (μ : Fin 4) : |x μ| ≤ euclidNormVec x :=
  Real.abs_le_sqrt (sq_apply_le_sumSq x μ)
theorem euclidNormVec_le_two_mul_norm (x : Fin 4 → ℝ) : euclidNormVec x ≤ 2 * ‖x‖ := by
  have hs : sumSq x ≤ (2 * ‖x‖) ^ 2 := by
    calc sumSq x ≤ ∑ _μ : Fin 4, ‖x‖ ^ 2 := Finset.sum_le_sum fun μ _ => by
          have h := norm_le_pi_norm x μ
          rw [Real.norm_eq_abs] at h
          rw [← sq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) h 2
      _ = (2 * ‖x‖) ^ 2 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  exact Real.sqrt_le_iff.2 ⟨by positivity, hs⟩
def sumSqMulLog (x : Fin 4 → ℝ) : ℝ := sumSq x * Real.log (sumSq x)
theorem logKernel_zero_eq_smul_sumSqMulLog :
    logKernel 0 = fun x => -(128 * Real.pi ^ 2)⁻¹ * sumSqMulLog x := by
  funext x
  unfold logKernel sumSqMulLog
  simp only [add_zero, euclidNormVec_sq]
  split_ifs with h
  · ring
  · have h0 : sumSq x = 0 := le_antisymm (not_lt.1 h) (sumSq_nonneg x)
    simp [h0]
def normMulLog (x : Fin 4 → ℝ) : ℝ := euclidNormVec x * Real.log (euclidNormVec x)
theorem tendsto_normMulLog_zero : Tendsto normMulLog (𝓝 0) (𝓝 0) := by
  have h := (Real.continuous_mul_log.comp continuous_euclidNormVec).tendsto 0
  have h0 : euclidNormVec (0 : Fin 4 → ℝ) = 0 := by simp [euclidNormVec]
  change Tendsto (fun x => euclidNormVec x * Real.log (euclidNormVec x)) (𝓝 0) (𝓝 0)
  simpa [h0, Function.comp_def] using h
theorem log_sumSq (x : Fin 4 → ℝ) :
    Real.log (sumSq x) = 2 * Real.log (euclidNormVec x) := by
  rw [← euclidNormVec_sq, Real.log_pow]
  norm_num
theorem norm_apply_mul_log_sumSq_le (x : Fin 4 → ℝ) (μ : Fin 4) :
    ‖x μ * Real.log (sumSq x)‖ ≤ 2 * |normMulLog x| := by
  have ht := euclidNormVec_nonneg x
  rw [Real.norm_eq_abs, abs_mul, log_sumSq, abs_mul, normMulLog, abs_mul, abs_of_nonneg ht]
  have h2 : |(2 : ℝ)| = 2 := by norm_num
  rw [h2]
  have := mul_le_mul_of_nonneg_right (abs_apply_le_euclidNormVec x μ)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (abs_nonneg (Real.log (euclidNormVec x))))
  nlinarith
theorem continuous_sumSq : Continuous sumSq := contDiff_sumSq.continuous
theorem continuous_apply_mul_log_sumSq (μ : Fin 4) :
    Continuous fun x : Fin 4 → ℝ => x μ * Real.log (sumSq x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst hx
    have hb : Tendsto (fun y : Fin 4 → ℝ => 2 * |normMulLog y|) (𝓝 0) (𝓝 0) := by
      simpa using tendsto_normMulLog_zero.abs.const_mul 2
    have h := squeeze_zero_norm (fun y => norm_apply_mul_log_sumSq_le y μ) hb
    simpa [ContinuousAt] using h
  · have hr : sumSq x ≠ 0 := fun h => hx (eq_zero_of_sumSq_eq_zero h)
    exact (continuous_apply μ).continuousAt.mul (continuous_sumSq.continuousAt.log hr)
def sumSqFDeriv (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ μ, (2 * x μ) • (ContinuousLinearMap.proj μ : (Fin 4 → ℝ) →L[ℝ] ℝ)
theorem hasFDerivAt_sumSq (x : Fin 4 → ℝ) :
    HasFDerivAt sumSq (sumSqFDeriv x) x := by
  have h : ∀ μ ∈ (Finset.univ : Finset (Fin 4)), HasFDerivAt (fun y : Fin 4 → ℝ => y μ ^ 2)
      ((2 * x μ) • (ContinuousLinearMap.proj μ : (Fin 4 → ℝ) →L[ℝ] ℝ)) x := by
    intro μ _
    have hp : HasFDerivAt (fun y : Fin 4 → ℝ => y μ)
        (ContinuousLinearMap.proj μ : (Fin 4 → ℝ) →L[ℝ] ℝ) x :=
      (ContinuousLinearMap.proj μ : (Fin 4 → ℝ) →L[ℝ] ℝ).hasFDerivAt
    have hfun : (fun y : Fin 4 → ℝ => y μ ^ 2) = fun y => y μ * y μ := by
      funext y
      ring
    rw [hfun]
    refine (hp.mul hp).congr_fderiv ?_
    ext1 v
    simp only [add_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    ring
  have hs := HasFDerivAt.fun_sum h
  exact hs
def sumSqMulLogFDeriv (x : Fin 4 → ℝ) : (Fin 4 → ℝ) →L[ℝ] ℝ :=
  ∑ μ, (2 * (x μ * Real.log (sumSq x) + x μ)) •
    (ContinuousLinearMap.proj μ : (Fin 4 → ℝ) →L[ℝ] ℝ)
theorem continuous_sumSqMulLogFDeriv : Continuous sumSqMulLogFDeriv :=
  continuous_finsetSum _ fun μ _ =>
    (continuous_const.mul ((continuous_apply_mul_log_sumSq μ).add (continuous_apply μ))).smul
      continuous_const
theorem hasFDerivAt_sumSqMulLog_of_ne_zero {x : Fin 4 → ℝ} (hx : x ≠ 0) :
    HasFDerivAt sumSqMulLog (sumSqMulLogFDeriv x) x := by
  have hr : sumSq x ≠ 0 := fun h => hx (eq_zero_of_sumSq_eq_zero h)
  have h1 := hasFDerivAt_sumSq x
  have h2 := h1.mul (h1.log hr)
  refine HasFDerivAt.congr_fderiv h2 ?_
  ext1 v
  simp only [sumSqMulLogFDeriv, sumSqFDeriv, add_apply,
    smul_apply, sum_apply, ContinuousLinearMap.proj_apply,
    smul_eq_mul, mul_inv_cancel_left₀ hr]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun μ _ => by ring
theorem hasFDerivAt_sumSqMulLog_zero :
    HasFDerivAt sumSqMulLog (sumSqMulLogFDeriv 0) (0 : Fin 4 → ℝ) := by
  have hD : sumSqMulLogFDeriv 0 = 0 := by simp [sumSqMulLogFDeriv]
  have h0 : sumSqMulLog (0 : Fin 4 → ℝ) = 0 := by simp [sumSqMulLog, sumSq]
  rw [hD, hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, h0, sub_zero, zero_apply]
  refine Asymptotics.isLittleO_iff.2 fun c hc => ?_
  have hev : ∀ᶠ y in 𝓝 (0 : Fin 4 → ℝ), |normMulLog y| < c / 4 := by
    have ht : Tendsto (fun y => |normMulLog y|) (𝓝 (0 : Fin 4 → ℝ)) (𝓝 0) := by
      simpa using tendsto_normMulLog_zero.abs
    exact ht.eventually (Iio_mem_nhds (by positivity))
  filter_upwards [hev] with y hy
  have ht := euclidNormVec_nonneg y
  have hid : ‖sumSqMulLog y‖ = 2 * euclidNormVec y * |normMulLog y| := by
    rw [sumSqMulLog, log_sumSq, ← euclidNormVec_sq, normMulLog, Real.norm_eq_abs, abs_mul,
      abs_mul, abs_mul, abs_of_nonneg ht, abs_of_nonneg (sq_nonneg _)]
    norm_num
    ring
  rw [hid]
  have hle := euclidNormVec_le_two_mul_norm y
  have hn := norm_nonneg y
  calc 2 * euclidNormVec y * |normMulLog y| ≤ 2 * (2 * ‖y‖) * |normMulLog y| := by gcongr
    _ = 4 * |normMulLog y| * ‖y‖ := by ring
    _ ≤ c * ‖y‖ := by
        apply mul_le_mul_of_nonneg_right _ hn
        linarith
theorem contDiff_one_sumSqMulLog : ContDiff ℝ 1 sumSqMulLog := by
  refine contDiff_one_iff_hasFDerivAt.2 ⟨sumSqMulLogFDeriv, continuous_sumSqMulLogFDeriv, ?_⟩
  intro x
  by_cases hx : x = 0
  · subst hx
    exact hasFDerivAt_sumSqMulLog_zero
  · exact hasFDerivAt_sumSqMulLog_of_ne_zero hx
theorem partialDerivR4_eq_fderiv {f : (Fin 4 → ℝ) → ℝ} (hf : Differentiable ℝ f) (μ : Fin 4) :
    partialDerivR4 μ f = fun x => fderiv ℝ f x (Pi.single μ (1 : ℝ)) := by
  funext x
  exact (hf x).lineDeriv_eq_fderiv
theorem contDiff_partialDerivR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) (μ : Fin 4) :
    ContDiff ℝ ∞ (partialDerivR4 μ f) := by
  rw [partialDerivR4_eq_fderiv (hf.differentiable (by simp)) μ]
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const
theorem contDiff_laplacianR4 {f : (Fin 4 → ℝ) → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (laplacianR4 f) :=
  ContDiff.sum fun μ _ => contDiff_partialDerivR4 (contDiff_partialDerivR4 hf μ) μ
theorem partialDerivR4_eventuallyEq {f g : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (h : f =ᶠ[𝓝 x] g)
    (μ : Fin 4) : partialDerivR4 μ f =ᶠ[𝓝 x] partialDerivR4 μ g := by
  filter_upwards [eventually_eventually_nhds.2 h] with y hy
  exact Filter.EventuallyEq.lineDeriv_eq hy
theorem laplacianR4_eventuallyEq {f g : (Fin 4 → ℝ) → ℝ} {x : Fin 4 → ℝ} (h : f =ᶠ[𝓝 x] g) :
    laplacianR4 f =ᶠ[𝓝 x] laplacianR4 g := by
  have hall : ∀ᶠ y in 𝓝 x, ∀ μ : Fin 4,
      partialDerivR4 μ (partialDerivR4 μ f) y = partialDerivR4 μ (partialDerivR4 μ g) y :=
    eventually_all.2 fun μ => partialDerivR4_eventuallyEq (partialDerivR4_eventuallyEq h μ) μ
  filter_upwards [hall] with y hy
  exact Finset.sum_congr rfl fun μ _ => hy μ
theorem isCompact_sq_euclidNormVec_le_half :
    IsCompact {x : Fin 4 → ℝ | euclidNormVec x ^ 2 ≤ 1 / 2} := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Fin 4 → ℝ) 1)
    (isClosed_le (continuous_euclidNormVec.pow 2) continuous_const) ?_
  intro x hx
  rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg zero_le_one]
  intro μ
  have h1 : x μ ^ 2 ≤ 1 := by
    have h2 := sq_apply_le_sumSq x μ
    have h3 : euclidNormVec x ^ 2 ≤ 1 / 2 := hx
    rw [euclidNormVec_sq] at h3
    linarith
  rw [Real.norm_eq_abs]
  exact (sq_le_one_iff_abs_le_one _).1 h1
end UnitKernelSupport
open UnitKernelSupport TorusMetric TestFunctions Filter in
theorem unitKernelRegularity_of_shellCutoff (hcut : shellCutoff_properties)
    (hlap : TripleLaplacianLogKernel) :
    UnitKernelRegularity := by
  obtain ⟨hsmooth, -, hone, hzero⟩ := hcut
  have hL : ContDiff ℝ 1 (logKernel 0) := by
    rw [logKernel_zero_eq_smul_sumSqMulLog]
    exact contDiff_const.mul contDiff_one_sumSqMulLog
  have hK : ContDiff ℝ 1 innerKernelUnit :=
    (hsmooth.of_le (by exact_mod_cast le_top)).mul hL
  have hR : ContDiff ℝ ∞ outerLogKernel := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x = 0
    · subst hx
      have hopen : IsOpen {y : Fin 4 → ℝ | euclidNormVec y < 1 / 2} :=
        isOpen_lt continuous_euclidNormVec continuous_const
      have hmem : (0 : Fin 4 → ℝ) ∈ {y : Fin 4 → ℝ | euclidNormVec y < 1 / 2} := by
        simp [euclidNormVec]
      have hev : outerLogKernel =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
        filter_upwards [hopen.mem_nhds hmem] with y hy
        simp [outerLogKernel, hone y (le_of_lt hy)]
      exact contDiffAt_const.congr_of_eventuallyEq hev
    · have hpos : 0 < euclidNormVec x ^ 2 + 0 := by
        rw [add_zero, euclidNormVec_sq]
        exact lt_of_le_of_ne (sumSq_nonneg x) fun h => hx (eq_zero_of_sumSq_eq_zero h.symm)
      have hopen : IsOpen {y : Fin 4 → ℝ | 0 < euclidNormVec y ^ 2 + 0} :=
        isOpen_lt continuous_const ((continuous_euclidNormVec.pow 2).add continuous_const)
      have hLx : ContDiffAt ℝ ∞ (logKernel 0) x :=
        ((hlap.1 0 le_rfl).1).contDiffAt (hopen.mem_nhds hpos)
      exact (contDiffAt_const.sub hsmooth.contDiffAt).mul hLx
  have hP : ContDiff ℝ ∞ outerKernelUnit :=
    contDiff_laplacianR4 (contDiff_laplacianR4 (contDiff_laplacianR4 hR))
  have hKz : ∀ x, 1 / 2 < euclidNormVec x ^ 2 → innerKernelUnit x = 0 := by
    intro x hx
    simp [innerKernelUnit, hzero x hx.le]
  have hPz : ∀ x, 1 / 2 < euclidNormVec x ^ 2 → outerKernelUnit x = 0 := by
    intro x hx
    have hopen : IsOpen {y : Fin 4 → ℝ | 1 / 2 < euclidNormVec y ^ 2} :=
      isOpen_lt continuous_const (continuous_euclidNormVec.pow 2)
    have hev : outerLogKernel =ᶠ[𝓝 x] logKernel 0 := by
      filter_upwards [hopen.mem_nhds hx] with y hy
      have hy' : 1 / 2 < euclidNormVec y ^ 2 := hy
      simp [outerLogKernel, hzero y hy'.le]
    have hne : x ≠ 0 := by
      rintro rfl
      norm_num [euclidNormVec] at hx
    have h3 := (laplacianR4_eventuallyEq (laplacianR4_eventuallyEq
      (laplacianR4_eventuallyEq hev))).eq_of_nhds
    have hfin := hlap.2 x hne
    exact h3.trans hfin
  refine ⟨hL, hR, hK, hP, ?_, ?_, fun x hx => ⟨hKz x hx, hPz x hx⟩⟩
  · exact HasCompactSupport.intro isCompact_sq_euclidNormVec_le_half fun x hx => hKz x (not_le.1 hx)
  · exact HasCompactSupport.intro isCompact_sq_euclidNormVec_le_half fun x hx => hPz x (not_le.1 hx)
end Parametrix
end YangMills.Construction
