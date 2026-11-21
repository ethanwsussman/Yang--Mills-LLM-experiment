import YangMills.Construction.Splines.CubicSplineBasicFacts
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Convolution
noncomputable section
namespace YangMills.Construction.Splines.CubicSplineLemmas
theorem realConvolution_eq_convolution (f g : ℝ → ℝ) :
    realConvolution f g = f ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] g := by
  funext s
  simp [realConvolution, MeasureTheory.convolution_def]
theorem measurableSet_quarterInterval : MeasurableSet quarterInterval := measurableSet_Icc
theorem quarterIntervalIndicator_of_mem {u : ℝ} (h : u ∈ quarterInterval) :
    quarterIntervalIndicator u = 1 := by
  simp [quarterIntervalIndicator, h]
theorem quarterIntervalIndicator_of_notMem {u : ℝ} (h : u ∉ quarterInterval) :
    quarterIntervalIndicator u = 0 := by
  simp [quarterIntervalIndicator, h]
theorem integrable_quarterIntervalIndicator : Integrable quarterIntervalIndicator :=
  (continuous_one.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_quarterInterval
theorem hasCompactSupport_quarterIntervalIndicator : HasCompactSupport quarterIntervalIndicator :=
  HasCompactSupport.intro (isCompact_Icc (a := (-(1 / 4) : ℝ)) (b := 1 / 4))
    (fun _ hx => quarterIntervalIndicator_of_notMem hx)
theorem quarterIntervalIndicator_mul_eq_indicator (s u : ℝ) :
    quarterIntervalIndicator u * quarterIntervalIndicator (s - u) =
      (Icc (max (-(1 / 4)) (s - 1 / 4)) (min (1 / 4) (s + 1 / 4))).indicator 1 u := by
  have key : (u ∈ quarterInterval ∧ s - u ∈ quarterInterval) ↔
      u ∈ Icc (max (-(1 / 4) : ℝ) (s - 1 / 4)) (min (1 / 4) (s + 1 / 4)) := by
    simp only [quarterInterval, mem_Icc, max_le_iff, le_min_iff]
    constructor
    · rintro ⟨⟨ha, hb⟩, hc, hd⟩
      exact ⟨⟨ha, by linarith⟩, hb, by linarith⟩
    · rintro ⟨⟨ha, hb⟩, hc, hd⟩
      exact ⟨⟨ha, hc⟩, by linarith, by linarith⟩
  by_cases h : u ∈ Icc (max (-(1 / 4) : ℝ) (s - 1 / 4)) (min (1 / 4) (s + 1 / 4))
  · obtain ⟨ha, hb⟩ := key.2 h
    rw [indicator_of_mem h, quarterIntervalIndicator_of_mem ha,
      quarterIntervalIndicator_of_mem hb]
    simp
  · rw [indicator_of_notMem h]
    by_cases ha : u ∈ quarterInterval
    · have hb : s - u ∉ quarterInterval := fun hb => h (key.1 ⟨ha, hb⟩)
      rw [quarterIntervalIndicator_of_notMem hb, mul_zero]
    · rw [quarterIntervalIndicator_of_notMem ha, zero_mul]
theorem integrable_quarterIntervalIndicator_mul (s : ℝ) :
    Integrable fun u => quarterIntervalIndicator u * quarterIntervalIndicator (s - u) := by
  simp_rw [quarterIntervalIndicator_mul_eq_indicator]
  exact (continuous_one.continuousOn.integrableOn_compact isCompact_Icc).integrable_indicator
    measurableSet_Icc
theorem tentFunction_eq (s : ℝ) : tentFunction s = max 0 (1 / 2 - |s|) := by
  have e : min (1 / 4 : ℝ) (s + 1 / 4) - max (-(1 / 4)) (s - 1 / 4) = 1 / 2 - |s| := by
    rcases le_total 0 s with h | h
    · rw [abs_of_nonneg h, min_eq_left (by linarith), max_eq_right (by linarith)]
      ring
    · rw [abs_of_nonpos h, min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  have h : tentFunction s = ∫ u, (Icc (max (-(1 / 4)) (s - 1 / 4)) (min (1 / 4) (s + 1 / 4))).indicator
      (1 : ℝ → ℝ) u := by
    simp_rw [← quarterIntervalIndicator_mul_eq_indicator]
    rfl
  rw [h, integral_indicator measurableSet_Icc]
  simp only [Pi.one_apply, setIntegral_const, smul_eq_mul, mul_one, Real.volume_real_Icc]
  rw [e, max_comm]
theorem tentFunction_nonneg (s : ℝ) : 0 ≤ tentFunction s := by
  rw [tentFunction_eq]
  exact le_max_left _ _
theorem tentFunction_neg (s : ℝ) : tentFunction (-s) = tentFunction s := by
  rw [tentFunction_eq, tentFunction_eq, abs_neg]
theorem tentFunction_eq_zero_of_le {s : ℝ} (h : 1 / 2 ≤ |s|) : tentFunction s = 0 := by
  rw [tentFunction_eq]
  exact max_eq_left (by linarith)
theorem continuous_tentFunction : Continuous tentFunction := by
  have : tentFunction = fun s => max 0 (1 / 2 - |s|) := funext tentFunction_eq
  rw [this]
  fun_prop
theorem hasCompactSupport_tentFunction : HasCompactSupport tentFunction :=
  HasCompactSupport.intro (isCompact_Icc (a := (-(1 / 2) : ℝ)) (b := 1 / 2)) (fun x hx => by
    apply tentFunction_eq_zero_of_le
    by_contra h
    exact hx (abs_le.mp (not_le.mp h).le))
theorem integrable_tentFunction : Integrable tentFunction :=
  continuous_tentFunction.integrable_of_hasCompactSupport hasCompactSupport_tentFunction
theorem tentFunction_eq_convolution :
    tentFunction = quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
      quarterIntervalIndicator :=
  realConvolution_eq_convolution _ _
theorem hasCompactSupport_tentFunction_sq : HasCompactSupport fun u => tentFunction u ^ 2 :=
  hasCompactSupport_tentFunction.comp_left (g := fun x : ℝ => x ^ 2) (by simp)
theorem integrable_tentFunction_sq : Integrable fun u => tentFunction u ^ 2 :=
  (continuous_tentFunction.pow 2).integrable_of_hasCompactSupport hasCompactSupport_tentFunction_sq
theorem integral_tentFunction_sq : ∫ u, tentFunction u ^ 2 = 1 / 12 := by
  have hsupp : ∀ x, x ∉ Icc (-(1 / 2) : ℝ) (1 / 2) → tentFunction x ^ 2 = 0 := by
    intro x hx
    have : 1 / 2 ≤ |x| := by
      by_contra h
      exact hx (abs_le.mp (not_le.mp h).le)
    rw [tentFunction_eq_zero_of_le this]
    norm_num
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u => tentFunction u ^ 2) volume a b :=
    fun a b => (continuous_tentFunction.pow 2).intervalIntegrable a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-(1 / 2)) 0) (hint 0 (1 / 2))]
  have hleft : ∫ u in (-(1 / 2) : ℝ)..0, tentFunction u ^ 2 =
      ∫ u in (-(1 / 2) : ℝ)..0, (1 / 2 + u) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have hlo := hu.1
    have hhi := hu.2
    simp only [tentFunction_eq, abs_of_nonpos hhi]
    rw [max_eq_right (by linarith)]
    ring
  have hright : ∫ u in (0 : ℝ)..(1 / 2), tentFunction u ^ 2 =
      ∫ u in (0 : ℝ)..(1 / 2), (1 / 2 - u) ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le (by norm_num)] at hu
    have hlo := hu.1
    have hhi := hu.2
    simp only [tentFunction_eq, abs_of_nonneg hlo]
    rw [max_eq_right (by linarith)]
  have hleftval : ∫ u in (-(1 / 2) : ℝ)..0, (1 / 2 + u) ^ 2 = 1 / 24 := by
    rw [intervalIntegral.integral_comp_add_left (fun x => x ^ 2) (1 / 2), integral_pow]
    norm_num
  have hrightval : ∫ u in (0 : ℝ)..(1 / 2), (1 / 2 - u) ^ 2 = 1 / 24 := by
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ 2) (1 / 2), integral_pow]
    norm_num
  rw [hleft, hright, hleftval, hrightval]
  norm_num
theorem realConvolution_tentFunction_zero :
    realConvolution tentFunction tentFunction 0 = 1 / 12 := by
  rw [← integral_tentFunction_sq]
  unfold realConvolution
  congr 1
  funext u
  rw [zero_sub, tentFunction_neg, sq]
theorem convolutionExists_tentFunction (f : ℝ → ℝ) (hf : LocallyIntegrable f) :
    ConvolutionExists f tentFunction (ContinuousLinearMap.mul ℝ ℝ) volume :=
  hasCompactSupport_tentFunction.convolutionExists_right _ hf continuous_tentFunction
theorem integrable_tentFunction_mul (s : ℝ) :
    Integrable fun u => tentFunction u * tentFunction (s - u) := by
  have := convolutionExists_tentFunction tentFunction integrable_tentFunction.locallyIntegrable s
  simpa [ConvolutionExistsAt] using this
theorem realConvolution_tentFunction_eq_assoc :
    realConvolution tentFunction tentFunction =
      quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume]
        (quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tentFunction) := by
  have hind : LocallyIntegrable (fun x => ‖quarterIntervalIndicator x‖) :=
    integrable_quarterIntervalIndicator.norm.locallyIntegrable
  have hcind : HasCompactSupport (fun x => ‖quarterIntervalIndicator x‖) :=
    hasCompactSupport_quarterIntervalIndicator.norm
  have hct : HasCompactSupport (fun x => ‖tentFunction x‖) := hasCompactSupport_tentFunction.norm
  have hnt : Continuous (fun x => ‖tentFunction x‖) := continuous_tentFunction.norm
  funext s
  rw [realConvolution_eq_convolution]
  nth_rewrite 1 [tentFunction_eq_convolution]
  refine convolution_assoc (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ)
    (ContinuousLinearMap.mul ℝ ℝ) (ContinuousLinearMap.mul ℝ ℝ) (fun x y z => ?_)
    integrable_quarterIntervalIndicator.aestronglyMeasurable
    integrable_quarterIntervalIndicator.aestronglyMeasurable
    integrable_tentFunction.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_) (Filter.Eventually.of_forall fun x => ?_) ?_
  · simp [mul_assoc]
  · simpa [ConvolutionExistsAt] using integrable_quarterIntervalIndicator_mul y
  · exact hct.convolutionExists_right _ hind hnt x
  · exact (hcind.convolution _ hct).convolutionExists_right _ hind
      (hct.continuous_convolution_right _ hind hnt) s
def tentAntiderivative (x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, tentFunction v
theorem hasDerivAt_tentAntiderivative (x : ℝ) :
    HasDerivAt tentAntiderivative (tentFunction x) x :=
  (continuous_tentFunction.integral_hasStrictDerivAt 0 x).hasDerivAt
theorem contDiff_tentAntiderivative : ContDiff ℝ 1 tentAntiderivative := by
  refine contDiff_one_iff_deriv.2
    ⟨fun x => (hasDerivAt_tentAntiderivative x).differentiableAt, ?_⟩
  have : deriv tentAntiderivative = tentFunction :=
    funext fun x => (hasDerivAt_tentAntiderivative x).deriv
  rw [this]
  exact continuous_tentFunction
theorem quarterIntervalIndicator_convolution_tentFunction (s : ℝ) :
    (quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tentFunction) s =
      tentAntiderivative (s + 1 / 4) - tentAntiderivative (s - 1 / 4) := by
  have h : ∀ u, quarterIntervalIndicator u * tentFunction (s - u) =
      quarterInterval.indicator (fun u => tentFunction (s - u)) u := by
    intro u
    by_cases hu : u ∈ quarterInterval
    · rw [indicator_of_mem hu, quarterIntervalIndicator_of_mem hu, one_mul]
    · rw [indicator_of_notMem hu, quarterIntervalIndicator_of_notMem hu, zero_mul]
  have hint : ∀ a b : ℝ, IntervalIntegrable tentFunction volume a b :=
    fun a b => continuous_tentFunction.intervalIntegrable a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (hint 0 (s - 1 / 4)) (hint (s - 1 / 4) (s + 1 / 4))
  rw [← realConvolution_eq_convolution]
  unfold realConvolution
  simp_rw [h]
  rw [integral_indicator measurableSet_quarterInterval, quarterInterval,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun x => tentFunction x) s]
  have e : s - -(1 / 4) = s + 1 / 4 := by ring
  rw [e]
  unfold tentAntiderivative
  linarith
theorem contDiff_quarterIntervalIndicator_convolution_tentFunction :
    ContDiff ℝ 1
      (quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tentFunction) := by
  have : (quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tentFunction) =
      fun s => tentAntiderivative (s + 1 / 4) - tentAntiderivative (s - 1 / 4) :=
    funext quarterIntervalIndicator_convolution_tentFunction
  rw [this]
  exact (contDiff_tentAntiderivative.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_tentAntiderivative.comp (contDiff_id.sub contDiff_const))
theorem contDiff_realConvolution_tentFunction :
    ContDiff ℝ 1 (realConvolution tentFunction tentFunction) := by
  rw [realConvolution_tentFunction_eq_assoc]
  have hc : HasCompactSupport
      (quarterIntervalIndicator ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] tentFunction) :=
    hasCompactSupport_quarterIntervalIndicator.convolution _ hasCompactSupport_tentFunction
  exact_mod_cast hc.contDiff_convolution_right (n := 1) (ContinuousLinearMap.mul ℝ ℝ)
    integrable_quarterIntervalIndicator.locallyIntegrable
    (by exact_mod_cast contDiff_quarterIntervalIndicator_convolution_tentFunction)
theorem cubicSpline_nonneg (s : ℝ) : 0 ≤ cubicSpline s := by
  unfold cubicSpline realConvolution
  exact mul_nonneg (by norm_num)
    (integral_nonneg fun u => mul_nonneg (tentFunction_nonneg _) (tentFunction_nonneg _))
theorem realConvolution_tentFunction_neg (s : ℝ) :
    realConvolution tentFunction tentFunction (-s) = realConvolution tentFunction tentFunction s := by
  unfold realConvolution
  rw [← integral_neg_eq_self]
  congr 1
  funext u
  have : -s - -u = -(s - u) := by ring
  rw [this, tentFunction_neg, tentFunction_neg]
theorem cubicSpline_neg (s : ℝ) : cubicSpline (-s) = cubicSpline s := by
  unfold cubicSpline
  rw [realConvolution_tentFunction_neg]
theorem cubicSpline_eq_zero_of_one_lt {s : ℝ} (h : 1 < |s|) : cubicSpline s = 0 := by
  have hz : ∀ u, tentFunction u * tentFunction (s - u) = 0 := by
    intro u
    by_cases hu : 1 / 2 ≤ |u|
    · rw [tentFunction_eq_zero_of_le hu, zero_mul]
    · have htri : |s| ≤ |s - u| + |u| := by
        have := abs_add_le (s - u) u
        simpa using this
      have hfar : 1 / 2 ≤ |s - u| := by
        push Not at hu
        linarith
      rw [tentFunction_eq_zero_of_le hfar, mul_zero]
  unfold cubicSpline realConvolution
  simp [hz]
theorem tsupport_cubicSpline_subset : tsupport cubicSpline ⊆ Icc (-1) 1 := by
  refine closure_minimal (fun s hs => ?_) isClosed_Icc
  by_contra h
  have hlt : 1 < |s| := by
    by_contra h'
    exact h (abs_le.mp (not_lt.mp h'))
  exact hs (cubicSpline_eq_zero_of_one_lt hlt)
theorem contDiff_cubicSpline : ContDiff ℝ 1 cubicSpline :=
  contDiff_const.mul contDiff_realConvolution_tentFunction
theorem realConvolution_tentFunction_le (s : ℝ) :
    realConvolution tentFunction tentFunction s ≤ 1 / 12 := by
  have hi : Integrable fun u => (tentFunction u ^ 2 + tentFunction (s - u) ^ 2) / 2 :=
    (integrable_tentFunction_sq.add (integrable_tentFunction_sq.comp_sub_left s)).div_const 2
  have hv : ∫ u, (tentFunction u ^ 2 + tentFunction (s - u) ^ 2) / 2 = 1 / 12 := by
    rw [integral_div, integral_add integrable_tentFunction_sq
        (integrable_tentFunction_sq.comp_sub_left s),
      integral_sub_left_eq_self (fun x => tentFunction x ^ 2) volume s, integral_tentFunction_sq]
    norm_num
  rw [← hv]
  refine integral_mono (integrable_tentFunction_mul s) hi fun u => ?_
  have := sq_nonneg (tentFunction u - tentFunction (s - u))
  simp only
  nlinarith
theorem cubicSpline_zero : cubicSpline 0 = 1 := by
  unfold cubicSpline
  rw [realConvolution_tentFunction_zero]
  norm_num
theorem cubicSpline_le_cubicSpline_zero (s : ℝ) : cubicSpline s ≤ cubicSpline 0 := by
  rw [cubicSpline_zero]
  unfold cubicSpline
  have := realConvolution_tentFunction_le s
  linarith
def fourierPhase (q s : ℝ) : ℂ := Complex.exp (Complex.I * (s : ℂ) * (q : ℂ))
def realFourierTransform (f : ℝ → ℝ) (q : ℝ) : ℂ := ∫ s : ℝ, (f s : ℂ) * fourierPhase q s
theorem norm_fourierPhase (q s : ℝ) : ‖fourierPhase q s‖ = 1 := by
  have h : Complex.I * (s : ℂ) * (q : ℂ) = ((s * q : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [fourierPhase, h, Complex.norm_exp_ofReal_mul_I]
theorem continuous_fourierPhase (q : ℝ) : Continuous (fourierPhase q) := by
  unfold fourierPhase
  fun_prop
theorem fourierPhase_mul (q u v : ℝ) :
    fourierPhase q u * fourierPhase q v = fourierPhase q (u + v) := by
  unfold fourierPhase
  rw [← Complex.exp_add]
  push_cast
  ring_nf
theorem integrable_mul_fourierPhase {f : ℝ → ℝ} (hf : Integrable f) (q : ℝ) :
    Integrable fun s => (f s : ℂ) * fourierPhase q s := by
  have hf' : Integrable fun s => (f s : ℂ) := hf.ofReal
  refine hf'.mono (hf'.aestronglyMeasurable.mul (continuous_fourierPhase q).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun s => ?_)
  simp [norm_fourierPhase]
theorem realFourierTransform_realConvolution {f g : ℝ → ℝ} (hf : Integrable f)
    (hg : Integrable g) (q : ℝ) :
    realFourierTransform (realConvolution f g) q =
      realFourierTransform f q * realFourierTransform g q := by
  have key := integral_convolution (ContinuousLinearMap.mul ℂ ℂ) (μ := volume) (ν := volume)
    (integrable_mul_fourierPhase hf q) (integrable_mul_fourierPhase hg q)
  have h : ∀ s : ℝ, (((fun s => (f s : ℂ) * fourierPhase q s)) ⋆[ContinuousLinearMap.mul ℂ ℂ, volume]
      (fun s => (g s : ℂ) * fourierPhase q s)) s =
        (realConvolution f g s : ℂ) * fourierPhase q s := by
    intro s
    rw [MeasureTheory.convolution_def]
    unfold realConvolution
    rw [← integral_complex_ofReal, ← integral_mul_const]
    congr 1
    funext u
    have : fourierPhase q u * fourierPhase q (s - u) = fourierPhase q s := by
      rw [fourierPhase_mul]
      congr 1
      ring
    simp only [ContinuousLinearMap.mul_apply']
    push_cast
    rw [← this]
    ring
  simp_rw [h] at key
  simpa [realFourierTransform] using key
theorem realFourierTransform_quarterIntervalIndicator (q : ℝ) :
    realFourierTransform quarterIntervalIndicator q = ((1 / 2 * Real.sinc (q / 4) : ℝ) : ℂ) := by
  have h : ∀ s : ℝ, (quarterIntervalIndicator s : ℂ) * fourierPhase q s =
      quarterInterval.indicator (fourierPhase q) s := by
    intro s
    by_cases hs : s ∈ quarterInterval
    · rw [indicator_of_mem hs, quarterIntervalIndicator_of_mem hs]
      simp
    · rw [indicator_of_notMem hs, quarterIntervalIndicator_of_notMem hs]
      simp
  unfold realFourierTransform
  simp_rw [h]
  rw [integral_indicator measurableSet_quarterInterval, quarterInterval,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  by_cases hq : q = 0
  · subst hq
    simp [fourierPhase]
    norm_num
  · have hc : Complex.I * (q : ℂ) ≠ 0 :=
      mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hq)
    have hw : ∀ s : ℝ, fourierPhase q s = Complex.exp (Complex.I * (q : ℂ) * (s : ℂ)) := by
      intro s
      unfold fourierPhase
      ring_nf
    simp_rw [hw]
    rw [integral_exp_mul_complex hc]
    have e1 : Complex.I * (q : ℂ) * ((1 / 4 : ℝ) : ℂ) = ((q / 4 : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have e2 : Complex.I * (q : ℂ) * ((-(1 / 4) : ℝ) : ℂ) = ((-(q / 4) : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [e1, e2, Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.sinc_of_ne_zero (div_ne_zero hq (by norm_num))]
    have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq
    push_cast
    field_simp
    ring_nf
theorem realFourierTransform_tentFunction (q : ℝ) :
    realFourierTransform tentFunction q = ((1 / 2 * Real.sinc (q / 4) : ℝ) : ℂ) ^ 2 := by
  have : realFourierTransform tentFunction q =
      realFourierTransform quarterIntervalIndicator q *
        realFourierTransform quarterIntervalIndicator q :=
    realFourierTransform_realConvolution integrable_quarterIntervalIndicator
      integrable_quarterIntervalIndicator q
  rw [this, realFourierTransform_quarterIntervalIndicator, sq]
theorem realFourierTransform_cubicSpline (q : ℝ) :
    realFourierTransform cubicSpline q = 3 / 4 * ((Real.sinc (q / 4) : ℝ) : ℂ) ^ 4 := by
  have h1 : realFourierTransform cubicSpline q =
      12 * realFourierTransform (realConvolution tentFunction tentFunction) q := by
    unfold realFourierTransform
    rw [← integral_const_mul]
    congr 1
    funext s
    unfold cubicSpline
    push_cast
    ring
  rw [h1, realFourierTransform_realConvolution integrable_tentFunction integrable_tentFunction,
    realFourierTransform_tentFunction]
  push_cast
  ring
theorem cubicSplineIntegral_eq : cubicSplineIntegral = 3 / 4 := by
  have h := realFourierTransform_cubicSpline 0
  have h0 : realFourierTransform cubicSpline 0 = (cubicSplineIntegral : ℂ) := by
    unfold realFourierTransform cubicSplineIntegral
    rw [← integral_complex_ofReal]
    simp [fourierPhase]
  rw [h0] at h
  simp only [zero_div, Real.sinc_zero] at h
  have h' : (cubicSplineIntegral : ℂ) = ((3 / 4 : ℝ) : ℂ) := by
    rw [h]
    push_cast
    ring
  exact Complex.ofReal_injective h'
theorem integral_cubicSpline_mul_eight : ∫ u : ℝ, cubicSpline (8 * u) = 3 / 32 := by
  rw [Measure.integral_comp_mul_left cubicSpline 8]
  change |(8 : ℝ)⁻¹| • cubicSplineIntegral = 3 / 32
  rw [cubicSplineIntegral_eq, abs_of_pos (by norm_num), smul_eq_mul]
  norm_num
theorem splineDensity_eq (s : ℝ) :
    splineDensity s = cubicSpline (8 * s) / ∫ u : ℝ, cubicSpline (8 * u) := by
  rw [integral_cubicSpline_mul_eight]
  unfold splineDensity
  ring
theorem splineDensity_nonneg (s : ℝ) : 0 ≤ splineDensity s :=
  mul_nonneg (by norm_num) (cubicSpline_nonneg _)
theorem splineDensity_neg (s : ℝ) : splineDensity (-s) = splineDensity s := by
  unfold splineDensity
  rw [mul_neg, cubicSpline_neg]
theorem contDiff_splineDensity : ContDiff ℝ 1 splineDensity :=
  contDiff_const.mul (contDiff_cubicSpline.comp (contDiff_const.mul contDiff_id))
theorem tsupport_splineDensity_subset : tsupport splineDensity ⊆ Icc (-(1 / 8)) (1 / 8) := by
  refine closure_minimal (fun s hs => ?_) isClosed_Icc
  by_contra h
  have hlt : 1 < |8 * s| := by
    by_contra h'
    obtain ⟨ha, hb⟩ := abs_le.mp (not_lt.mp h')
    exact h ⟨by linarith, by linarith⟩
  apply hs
  unfold splineDensity
  rw [cubicSpline_eq_zero_of_one_lt hlt, mul_zero]
theorem integral_splineDensity : ∫ s : ℝ, splineDensity s = 1 := by
  unfold splineDensity
  rw [integral_const_mul, integral_cubicSpline_mul_eight]
  norm_num
theorem cubicSplineBasicFacts_holds : CubicSplineBasicFacts := by
  refine ⟨⟨tentFunction_eq, realConvolution_tentFunction_zero, fun s => ?_⟩,
    ⟨cubicSpline_nonneg, cubicSpline_neg, tsupport_cubicSpline_subset, contDiff_cubicSpline,
      cubicSpline_le_cubicSpline_zero, cubicSpline_zero⟩,
    ⟨fun q => ?_, cubicSplineIntegral_eq, by rw [cubicSplineIntegral_eq]; norm_num⟩,
    ⟨splineDensity_nonneg, splineDensity_neg, contDiff_splineDensity,
      tsupport_splineDensity_subset, integral_splineDensity, splineDensity_eq⟩⟩
  · rw [realConvolution_tentFunction_zero]
    unfold cubicSpline
    ring
  · have h := realFourierTransform_cubicSpline q
    have hc : (cubicSplineIntegral : ℂ) = 3 / 4 := by
      rw [cubicSplineIntegral_eq]
      push_cast
      ring
    rw [hc]
    exact h
end YangMills.Construction.Splines.CubicSplineLemmas
