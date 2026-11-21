import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctionsProof
import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBounds
import YangMills.Construction.Continuum.NormFactorialInequalities
import Mathlib
open Set MeasureTheory Filter Topology
open scoped ContDiff
noncomputable section
namespace YangMills.Construction.BumpFunctions.GevreyBumps
lemma contDiff_bumpProfile : ContDiff ℝ ∞ bumpProfile := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.contDiff_expBump <;> assumption
def complexExpNegInv (ζ : ℂ) : ℂ := Complex.exp (-ζ⁻¹)
def rightHalfPlane : Set ℂ := {ζ | 0 < ζ.re}
lemma isOpen_rightHalfPlane : IsOpen rightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re
lemma ne_zero_of_mem_rightHalfPlane {ζ : ℂ} (h : ζ ∈ rightHalfPlane) : ζ ≠ 0 := by
  rintro rfl
  simp [rightHalfPlane] at h
lemma differentiableOn_complexExpNegInv : DifferentiableOn ℂ complexExpNegInv rightHalfPlane := by
  intro ζ hζ
  have h0 := ne_zero_of_mem_rightHalfPlane hζ
  have : DifferentiableAt ℂ complexExpNegInv ζ := by
    unfold complexExpNegInv
    exact (differentiableAt_inv h0).neg.cexp
  exact this.differentiableWithinAt
lemma analyticOnNhd_iteratedDeriv_complexExpNegInv (r : ℕ) :
    AnalyticOnNhd ℂ (iteratedDeriv r complexExpNegInv) rightHalfPlane := by
  have h := (differentiableOn_complexExpNegInv.analyticOnNhd isOpen_rightHalfPlane).iterated_deriv r
  rwa [← iteratedDeriv_eq_iterate] at h
lemma bumpProfile_of_pos {t : ℝ} (ht : 0 < t) : bumpProfile t = Real.exp (-t⁻¹) := by
  simp [bumpProfile, expNegInv, ht, neg_div, one_div]
lemma ofReal_iteratedDeriv_bumpProfile_of_pos (r : ℕ) :
    ∀ t : ℝ, 0 < t →
      ((iteratedDeriv r bumpProfile t : ℝ) : ℂ) = iteratedDeriv r complexExpNegInv (t : ℂ) := by
  induction r with
  | zero =>
    intro t ht
    simp only [iteratedDeriv_zero, bumpProfile_of_pos ht, complexExpNegInv]
    push_cast
    rfl
  | succ r ih =>
    intro t ht
    have hmem : (t : ℂ) ∈ rightHalfPlane := by simpa [rightHalfPlane] using ht
    have hF : HasDerivAt (iteratedDeriv r complexExpNegInv)
        (deriv (iteratedDeriv r complexExpNegInv) (t : ℂ)) (t : ℂ) :=
      ((analyticOnNhd_iteratedDeriv_complexExpNegInv r _ hmem).differentiableAt).hasDerivAt
    have hFr := hF.comp_ofReal
    have hg : DifferentiableAt ℝ (iteratedDeriv r bumpProfile) t :=
      (contDiff_bumpProfile.differentiable_iteratedDeriv r (by exact_mod_cast WithTop.coe_lt_top _)) t
    have hgc := hg.hasDerivAt.ofReal_comp
    have hev : (fun y : ℝ => ((iteratedDeriv r bumpProfile y : ℝ) : ℂ)) =ᶠ[𝓝 t]
        fun y : ℝ => iteratedDeriv r complexExpNegInv (y : ℂ) := by
      filter_upwards [lt_mem_nhds ht] with y hy using ih y hy
    have := (hFr.congr_of_eventuallyEq hev).unique hgc
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact this.symm
lemma norm_iteratedDeriv_complexExpNegInv_le (r : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv r complexExpNegInv (t : ℂ)‖ ≤
      r.factorial * Real.exp (-(2 / (9 * t))) / (t / 2) ^ r := by
  have hR : 0 < t / 2 := by positivity
  have hsub : ∀ ζ ∈ Metric.closedBall (t : ℂ) (t / 2), t / 2 ≤ ζ.re ∧ ‖ζ‖ ≤ 3 * t / 2 := by
    intro ζ hζ
    have hd : ‖ζ - t‖ ≤ t / 2 := by simpa [dist_eq_norm] using hζ
    have h1 : |(ζ - t).re| ≤ t / 2 := (Complex.abs_re_le_norm _).trans hd
    have h2 : (ζ - t).re = ζ.re - t := by simp
    rw [h2] at h1
    have h3 := (abs_le.mp h1).1
    refine ⟨by linarith, ?_⟩
    have h4 : ‖ζ‖ ≤ ‖ζ - t‖ + ‖(t : ℂ)‖ := by
      simpa using norm_add_le (ζ - t) (t : ℂ)
    have h5 : ‖(t : ℂ)‖ = t := by simp [abs_of_pos ht]
    linarith
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r hR ?_ ?_
  · have hd : DifferentiableOn ℂ complexExpNegInv (Metric.closedBall (t : ℂ) (t / 2)) := by
      refine differentiableOn_complexExpNegInv.mono ?_
      intro ζ hζ
      have := (hsub ζ hζ).1
      show 0 < ζ.re
      linarith
    exact hd.diffContOnCl_ball subset_rfl
  · intro ζ hζ
    obtain ⟨h1, h2⟩ := hsub ζ (Metric.sphere_subset_closedBall hζ)
    have hre : 0 < ζ.re := by linarith
    have hn : 0 < ‖ζ‖ := by
      have : ζ ≠ 0 := by
        rintro rfl
        simp at hre
      exact norm_pos_iff.mpr this
    have hnorm : ‖complexExpNegInv ζ‖ = Real.exp (-(ζ.re / Complex.normSq ζ)) := by
      simp [complexExpNegInv, Complex.norm_exp, Complex.inv_re]
    rw [hnorm]
    apply Real.exp_le_exp.mpr
    apply neg_le_neg
    rw [Complex.normSq_eq_norm_sq]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h3 : ‖ζ‖ ^ 2 ≤ (3 * t / 2) ^ 2 := pow_le_pow_left₀ hn.le h2 2
    nlinarith [mul_pos ht ht]
lemma iteratedDeriv_bumpProfile_of_neg (r : ℕ) {t : ℝ} (ht : t < 0) :
    iteratedDeriv r bumpProfile t = 0 := by
  have hev : bumpProfile =ᶠ[𝓝 t] fun _ => (0 : ℝ) := by
    filter_upwards [gt_mem_nhds ht] with y hy
    simp [bumpProfile, expNegInv, not_lt.mpr hy.le]
  rw [hev.iteratedDeriv_eq r]
  simp
lemma iteratedDeriv_bumpProfile_of_nonpos (r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv r bumpProfile t = 0 := by
  rcases ht.lt_or_eq with ht | rfl
  · exact iteratedDeriv_bumpProfile_of_neg r ht
  · have hc : Continuous (iteratedDeriv r bumpProfile) :=
      contDiff_bumpProfile.continuous_iteratedDeriv r (by exact_mod_cast le_top)
    have h1 : Tendsto (iteratedDeriv r bumpProfile) (𝓝[<] 0) (𝓝 (iteratedDeriv r bumpProfile 0)) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (iteratedDeriv r bumpProfile) (𝓝[<] 0) (𝓝 0) := by
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (iteratedDeriv_bumpProfile_of_neg r hy).symm
    exact tendsto_nhds_unique h1 h2
lemma abs_iteratedDeriv_bumpProfile_le
    (hexp : ∀ (s : ℕ) (v : ℝ), 0 ≤ v → v ^ s ≤ (s.factorial : ℝ) * Real.exp v)
    (r : ℕ) (t : ℝ) :
    |iteratedDeriv r bumpProfile t| ≤ gevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [iteratedDeriv_bumpProfile_of_nonpos r ht]
    simp only [abs_zero, gevreyConst]
    positivity
  · have h1 : |iteratedDeriv r bumpProfile t| = ‖iteratedDeriv r complexExpNegInv (t : ℂ)‖ := by
      rw [← ofReal_iteratedDeriv_bumpProfile_of_pos r t ht]
      simp
    rw [h1]
    refine (norm_iteratedDeriv_complexExpNegInv_le r ht).trans ?_
    set v : ℝ := 2 / (9 * t) with hv
    have hv0 : 0 ≤ v := by positivity
    have h2 := hexp r v hv0
    have h3 : (t / 2)⁻¹ = 9 * v := by
      rw [hv]
      field_simp
    rw [div_eq_mul_inv, ← inv_pow, h3, mul_pow]
    have h4 : Real.exp (-v) * Real.exp v = 1 := by
      rw [← Real.exp_add]; simp
    have h5 : Real.exp (-v) * v ^ r ≤ r.factorial := by
      calc Real.exp (-v) * v ^ r ≤ Real.exp (-v) * ((r.factorial : ℝ) * Real.exp v) :=
            mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
        _ = r.factorial := by
            rw [mul_left_comm, h4, mul_one]
    calc (r.factorial : ℝ) * Real.exp (-v) * (9 ^ r * v ^ r)
        = (r.factorial * 9 ^ r) * (Real.exp (-v) * v ^ r) := by ring
      _ ≤ (r.factorial * 9 ^ r) * r.factorial :=
          mul_le_mul_of_nonneg_left h5 (by positivity)
      _ = gevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
          simp only [gevreyConst]; ring
lemma abs_iteratedDeriv_mul_le_of_gevrey {f₁ f₂ : ℝ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (h₁ : ContDiff ℝ ∞ f₁) (h₂ : ContDiff ℝ ∞ f₂)
    (b₁ : ∀ (r : ℕ) (t : ℝ), |iteratedDeriv r f₁ t| ≤ b ^ r * (r.factorial : ℝ) ^ 2)
    (b₂ : ∀ (r : ℕ) (t : ℝ), |iteratedDeriv r f₂ t| ≤ b ^ r * (r.factorial : ℝ) ^ 2)
    (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (fun x => f₁ x * f₂ x) t| ≤ (2 * b) ^ r * (r.factorial : ℝ) ^ 2 := by
  have c₁ : ContDiffAt ℝ r f₁ t := (h₁.of_le (by exact_mod_cast le_top)).contDiffAt
  have c₂ : ContDiffAt ℝ r f₂ t := (h₂.of_le (by exact_mod_cast le_top)).contDiffAt
  rw [iteratedDeriv_fun_mul c₁ c₂]
  calc |∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * iteratedDeriv i f₁ t *
          iteratedDeriv (r - i) f₂ t|
      ≤ ∑ i ∈ Finset.range (r + 1), |(r.choose i : ℝ) * iteratedDeriv i f₁ t *
          iteratedDeriv (r - i) f₂ t| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (b ^ r * (r.factorial : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        have hfac : (i.factorial : ℝ) * ((r - i).factorial : ℝ) ≤ r.factorial := by
          exact_mod_cast Nat.le_of_dvd r.factorial_pos (Nat.factorial_mul_factorial_dvd_factorial hir)
        have hsq : (i.factorial : ℝ) ^ 2 * ((r - i).factorial : ℝ) ^ 2 ≤ (r.factorial : ℝ) ^ 2 := by
          rw [← mul_pow]
          exact pow_le_pow_left₀ (by positivity) hfac 2
        have hbb : b ^ i * b ^ (r - i) = b ^ r := by
          rw [← pow_add, Nat.add_sub_cancel' hir]
        rw [abs_mul, abs_mul, Nat.abs_cast, mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc |iteratedDeriv i f₁ t| * |iteratedDeriv (r - i) f₂ t|
            ≤ (b ^ i * (i.factorial : ℝ) ^ 2) * (b ^ (r - i) * ((r - i).factorial : ℝ) ^ 2) :=
              mul_le_mul (b₁ i t) (b₂ _ t) (abs_nonneg _) (by positivity)
          _ = b ^ r * ((i.factorial : ℝ) ^ 2 * ((r - i).factorial : ℝ) ^ 2) := by
              rw [← hbb]; ring
          _ ≤ b ^ r * (r.factorial : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (2 * b) ^ r * (r.factorial : ℝ) ^ 2 := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        ring
def stepWeight (τ : ℝ) : ℝ := bumpProfile τ * bumpProfile (1 - τ)
def bumpWeight (t : ℝ) : ℝ := bumpProfile (t + 1 / 4) * bumpProfile (1 / 4 - t)
lemma contDiff_stepWeight : ContDiff ℝ ∞ stepWeight :=
  contDiff_bumpProfile.mul (contDiff_bumpProfile.comp (by fun_prop))
lemma contDiff_bumpWeight : ContDiff ℝ ∞ bumpWeight :=
  (contDiff_bumpProfile.comp (by fun_prop)).mul (contDiff_bumpProfile.comp (by fun_prop))
def BumpProfileGevrey : Prop :=
  ∀ (r : ℕ) (t : ℝ), |iteratedDeriv r bumpProfile t| ≤ gevreyConst ^ r * (r.factorial : ℝ) ^ 2
lemma gevreyConst_nonneg : 0 ≤ gevreyConst := by norm_num [gevreyConst]
lemma abs_iteratedDeriv_stepWeight_le (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r stepWeight t| ≤ blockConst ^ r * (r.factorial : ℝ) ^ 2 := by
  refine abs_iteratedDeriv_mul_le_of_gevrey gevreyConst_nonneg contDiff_bumpProfile
    (contDiff_bumpProfile.comp (by fun_prop)) hg ?_ r t
  intro r t
  have h := congrFun (iteratedDeriv_comp_const_sub r bumpProfile (1 : ℝ)) t
  simp only [smul_eq_mul] at h
  show |iteratedDeriv r (fun z => bumpProfile (1 - z)) t| ≤ _
  rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact hg r _
lemma abs_iteratedDeriv_bumpWeight_le (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r bumpWeight t| ≤ blockConst ^ r * (r.factorial : ℝ) ^ 2 := by
  refine abs_iteratedDeriv_mul_le_of_gevrey gevreyConst_nonneg
    (contDiff_bumpProfile.comp (by fun_prop)) (contDiff_bumpProfile.comp (by fun_prop)) ?_ ?_ r t
  · intro r t
    have h := congrFun (iteratedDeriv_comp_add_const r bumpProfile (1 / 4 : ℝ)) t
    show |iteratedDeriv r (fun z => bumpProfile (z + 1 / 4)) t| ≤ _
    rw [h]
    exact hg r _
  · intro r t
    have h := congrFun (iteratedDeriv_comp_const_sub r bumpProfile (1 / 4 : ℝ)) t
    simp only [smul_eq_mul] at h
    show |iteratedDeriv r (fun z => bumpProfile (1 / 4 - z)) t| ≤ _
    rw [h, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact hg r _
section Integrals
variable (hn : ExpNegInvIntegralBounds)
include hn
lemma stepWeight_nonneg (τ : ℝ) : 0 ≤ stepWeight τ := (hn.2.1.2.2.1 τ).1
lemma bumpWeight_nonneg (t : ℝ) : 0 ≤ bumpWeight t := (hn.2.1.2.2.2.1 t).1
lemma stepWeight_eq_zero_of_not_mem {τ : ℝ} (h : τ ∉ Ioo (0 : ℝ) 1) : stepWeight τ = 0 :=
  hn.2.1.2.2.2.2.2.1 τ h
lemma bumpWeight_eq_zero_of_not_mem {t : ℝ} (h : t ∉ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    bumpWeight t = 0 :=
  hn.2.1.2.2.2.2.2.2.2 t h
lemma stepIntegralConst_pos : 0 < stepIntegralConst := (hn.2.2.1 1 one_pos le_rfl).1
lemma bumpIntegralConst_eq_intervalIntegral :
    bumpIntegralConst = ∫ t in (-(1 / 4) : ℝ)..(1 / 4), bumpWeight t := by
  rw [intervalIntegral.integral_of_le (by norm_num)]
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  exact bumpWeight_eq_zero_of_not_mem hn fun h => hx ⟨h.1, h.2.le⟩
lemma bumpIntegralConst_pos : 0 < bumpIntegralConst := by
  rw [bumpIntegralConst_eq_intervalIntegral hn]
  exact hn.2.2.2.1
lemma integrable_stepWeight : Integrable stepWeight :=
  contDiff_stepWeight.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.intro (isCompact_Icc (a := (0 : ℝ)) (b := 1))
      fun _ hx => stepWeight_eq_zero_of_not_mem hn fun h => hx ⟨h.1.le, h.2.le⟩)
end Integrals
lemma hasDerivAt_integral_from {u : ℝ → ℝ} (hu : Continuous u) (a t : ℝ) :
    HasDerivAt (fun t => ∫ x in a..t, u x) (u t) t :=
  (hu.integral_hasStrictDerivAt a t).hasDerivAt
lemma deriv_integral_from {u : ℝ → ℝ} (hu : Continuous u) (a : ℝ) :
    deriv (fun t => ∫ x in a..t, u x) = u :=
  funext fun t => (hasDerivAt_integral_from hu a t).deriv
lemma contDiff_integral_from {u : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (a : ℝ) :
    ContDiff ℝ ∞ (fun t => ∫ x in a..t, u x) := by
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hasDerivAt_integral_from hu.continuous a t).differentiableAt, ?_⟩
  rw [deriv_integral_from hu.continuous]
  exact hu
lemma iteratedDeriv_succ_integral_from {u : ℝ → ℝ} (hu : Continuous u) (a : ℝ) (r : ℕ) :
    iteratedDeriv (r + 1) (fun t => ∫ x in a..t, u x) = iteratedDeriv r u := by
  rw [iteratedDeriv_succ', deriv_integral_from hu]
section Step
variable (hn : ExpNegInvIntegralBounds)
include hn
lemma smoothStep_eq_integral :
    smoothStep = fun t => ∫ x in (0 : ℝ)..t, stepIntegralConst⁻¹ * stepWeight x := by
  funext t
  have hI := integrable_stepWeight hn
  have h := intervalIntegral.integral_Iic_sub_Iic (a := 0) (b := t) hI.integrableOn hI.integrableOn
  have h0 : ∫ x in Iic (0 : ℝ), stepWeight x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      stepWeight_eq_zero_of_not_mem hn fun hh => absurd hh.1 (not_lt.mpr hx)
  rw [h0, sub_zero] at h
  rw [intervalIntegral.integral_const_mul, ← h]
  show 1 / stepIntegralConst * _ = _
  rw [one_div]
  rfl
lemma hasDerivAt_smoothStep (t : ℝ) :
    HasDerivAt smoothStep (stepIntegralConst⁻¹ * stepWeight t) t := by
  rw [smoothStep_eq_integral hn]
  exact hasDerivAt_integral_from (u := fun x => stepIntegralConst⁻¹ * stepWeight x)
    (continuous_const.mul contDiff_stepWeight.continuous) 0 t
lemma contDiff_smoothStep : ContDiff ℝ ∞ smoothStep := by
  rw [smoothStep_eq_integral hn]
  exact contDiff_integral_from (contDiff_const.mul contDiff_stepWeight) 0
lemma monotone_smoothStep : Monotone smoothStep := by
  refine monotone_of_deriv_nonneg (contDiff_smoothStep hn |>.differentiable (by simp)) fun t => ?_
  rw [(hasDerivAt_smoothStep hn t).deriv]
  exact mul_nonneg (inv_nonneg.mpr (stepIntegralConst_pos hn).le) (stepWeight_nonneg hn t)
lemma smoothStep_of_nonpos {t : ℝ} (ht : t ≤ 0) : smoothStep t = 0 := by
  have h0 : ∫ x in Iic t, stepWeight x = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx =>
      stepWeight_eq_zero_of_not_mem hn fun hh =>
        absurd (hh.1.trans_le (mem_Iic.mp hx)) (not_lt.mpr ht)
  show 1 / stepIntegralConst * ∫ τ in Iic t, stepWeight τ = 0
  rw [h0, mul_zero]
lemma smoothStep_one : smoothStep 1 = 1 := by
  rw [smoothStep_eq_integral hn]
  show ∫ x in (0 : ℝ)..1, stepIntegralConst⁻¹ * stepWeight x = 1
  rw [intervalIntegral.integral_const_mul]
  show stepIntegralConst⁻¹ * stepIntegralConst = 1
  exact inv_mul_cancel₀ (stepIntegralConst_pos hn).ne'
lemma smoothStep_of_one_le {t : ℝ} (ht : 1 ≤ t) : smoothStep t = 1 := by
  have h1 : ∫ x in (1 : ℝ)..t, stepIntegralConst⁻¹ * stepWeight x = 0 := by
    rw [intervalIntegral.integral_const_mul]
    have : ∫ x in (1 : ℝ)..t, stepWeight x = ∫ x in (1 : ℝ)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le ht] at hx
      exact stepWeight_eq_zero_of_not_mem hn fun hh => absurd hh.2 (not_lt.mpr hx.1)
    rw [this]
    simp
  have hi : ∀ a b : ℝ,
      IntervalIntegrable (fun x => stepIntegralConst⁻¹ * stepWeight x) volume a b := fun a b =>
    (continuous_const.mul contDiff_stepWeight.continuous).intervalIntegrable a b
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi 0 1) (hi 1 t)
  have h3 := smoothStep_one hn
  rw [smoothStep_eq_integral hn] at h3 ⊢
  simp only at h3 ⊢
  rw [← h2, h1, add_zero, h3]
lemma smoothStep_pos {t : ℝ} (ht : 0 < t) : 0 < smoothStep t := by
  have h1 : 0 < min t 1 := lt_min ht one_pos
  have h2 : 0 < smoothStep (min t 1) := by
    rw [smoothStep_eq_integral hn]
    simp only
    rw [intervalIntegral.integral_const_mul]
    exact mul_pos (inv_pos.mpr (stepIntegralConst_pos hn)) (hn.2.2.1 _ h1 (min_le_right _ _)).1
  exact h2.trans_le (monotone_smoothStep hn (min_le_left _ _))
lemma smoothStep_mem_Icc (t : ℝ) : smoothStep t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rcases le_or_gt t 0 with h | h
    · exact (smoothStep_of_nonpos hn h).ge
    · exact (smoothStep_pos hn h).le
  · calc smoothStep t ≤ smoothStep (max t 1) := monotone_smoothStep hn (le_max_left _ _)
      _ = 1 := smoothStep_of_one_le hn (le_max_right _ _)
end Step
lemma one_le_integralConstBound : 1 ≤ integralConstBound := le_max_left _ _
lemma inv_stepIntegralConst_le : stepIntegralConst⁻¹ ≤ integralConstBound :=
  (le_max_left _ _).trans (le_max_right _ _)
lemma inv_bumpIntegralConst_le : bumpIntegralConst⁻¹ ≤ integralConstBound :=
  (le_max_right _ _).trans (le_max_right _ _)
lemma blockConst_eq : blockConst = 18 := by
  norm_num [blockConst, gevreyConst]
lemma mul_abs_le_of_gevrey_succ {a x : ℝ} (ha : 0 ≤ a) (haA : a ≤ integralConstBound) (r : ℕ)
    (hx : |x| ≤ blockConst ^ r * (r.factorial : ℝ) ^ 2) :
    a * |x| ≤ integralConstBound * blockConst ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2 := by
  have hC : (1 : ℝ) ≤ blockConst := by rw [blockConst_eq]; norm_num
  have hA : (0 : ℝ) ≤ integralConstBound := by linarith [one_le_integralConstBound]
  have h1 : blockConst ^ r ≤ blockConst ^ (r + 1) :=
    pow_le_pow_right₀ hC (Nat.le_succ r)
  have h2 : (r.factorial : ℝ) ≤ ((r + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ r)
  have h3 : (r.factorial : ℝ) ^ 2 ≤ ((r + 1).factorial : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  calc a * |x| ≤ integralConstBound * (blockConst ^ r * (r.factorial : ℝ) ^ 2) :=
        mul_le_mul haA hx (abs_nonneg _) hA
    _ ≤ integralConstBound * (blockConst ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hA
        exact mul_le_mul h1 h3 (by positivity) (by positivity)
    _ = _ := by ring
lemma abs_iteratedDeriv_smoothStep_le (hn : ExpNegInvIntegralBounds)
    (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r smoothStep t| ≤
      integralConstBound * blockConst ^ r * (r.factorial : ℝ) ^ 2 := by
  cases r with
  | zero =>
    have h := smoothStep_mem_Icc hn t
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg h.1]
    exact h.2.trans one_le_integralConstBound
  | succ r =>
    have hu : Continuous fun x => stepIntegralConst⁻¹ * stepWeight x :=
      continuous_const.mul contDiff_stepWeight.continuous
    rw [smoothStep_eq_integral hn, iteratedDeriv_succ_integral_from hu 0 r,
      iteratedDeriv_const_mul_field, abs_mul,
      abs_of_nonneg (inv_nonneg.mpr (stepIntegralConst_pos hn).le)]
    exact mul_abs_le_of_gevrey_succ (inv_nonneg.mpr (stepIntegralConst_pos hn).le)
      inv_stepIntegralConst_le r (abs_iteratedDeriv_stepWeight_le hg r t)
section Even
variable (hn : ExpNegInvIntegralBounds)
include hn
omit hn in
lemma evenSmoothStep_eventuallyEq_of_pos {x : ℝ} (hx : 0 < x) :
    evenSmoothStep =ᶠ[𝓝 x] fun t => smoothStep (t - 1) := by
  filter_upwards [lt_mem_nhds hx] with y hy
  simp only [evenSmoothStep, abs_of_pos hy]
omit hn in
lemma evenSmoothStep_eventuallyEq_of_neg {x : ℝ} (hx : x < 0) :
    evenSmoothStep =ᶠ[𝓝 x] fun t => smoothStep (-1 - t) := by
  filter_upwards [gt_mem_nhds hx] with y hy
  simp only [evenSmoothStep, abs_of_neg hy]
  congr 1
  ring
lemma evenSmoothStep_eventuallyEq_zero : evenSmoothStep =ᶠ[𝓝 0] fun _ => (0 : ℝ) := by
  filter_upwards [Ioo_mem_nhds (show (-1 : ℝ) < 0 by norm_num) one_pos] with y hy
  have : |y| < 1 := abs_lt.mpr hy
  exact smoothStep_of_nonpos hn (by linarith)
lemma contDiff_evenSmoothStep : ContDiff ℝ ∞ evenSmoothStep := by
  have hs := contDiff_smoothStep hn
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact ((hs.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ => -1 - t)).contDiffAt).congr_of_eventuallyEq
      (evenSmoothStep_eventuallyEq_of_neg hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (evenSmoothStep_eventuallyEq_zero hn)
  · exact ((hs.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ => t - 1)).contDiffAt).congr_of_eventuallyEq
      (evenSmoothStep_eventuallyEq_of_pos hx)
lemma abs_iteratedDeriv_evenSmoothStep_le (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r evenSmoothStep t| ≤
      integralConstBound * blockConst ^ r * (r.factorial : ℝ) ^ 2 := by
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · rw [(evenSmoothStep_eventuallyEq_of_neg ht).iteratedDeriv_eq r,
      congrFun (iteratedDeriv_comp_const_sub r smoothStep (-1 : ℝ)) t, smul_eq_mul,
      abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_iteratedDeriv_smoothStep_le hn hg r _
  · rw [(evenSmoothStep_eventuallyEq_zero hn).iteratedDeriv_eq r]
    have hA : (0 : ℝ) ≤ integralConstBound := by linarith [one_le_integralConstBound]
    have hC : (0 : ℝ) ≤ blockConst := by rw [blockConst_eq]; norm_num
    simp only [iteratedDeriv_const]
    split_ifs <;> simp <;> positivity
  · rw [(evenSmoothStep_eventuallyEq_of_pos ht).iteratedDeriv_eq r,
      congrFun (iteratedDeriv_comp_sub_const r smoothStep (1 : ℝ)) t]
    exact abs_iteratedDeriv_smoothStep_le hn hg r _
end Even
lemma normalizedBump_apply (t : ℝ) : normalizedBump t = bumpIntegralConst⁻¹ * bumpWeight t := by
  simp only [normalizedBump, bumpWeight, one_div, mul_assoc]
lemma normalizedBump_eq : normalizedBump = fun t => bumpIntegralConst⁻¹ * bumpWeight t :=
  funext normalizedBump_apply
lemma contDiff_normalizedBump : ContDiff ℝ ∞ normalizedBump := by
  rw [normalizedBump_eq]
  exact contDiff_const.mul contDiff_bumpWeight
def bumpPrimitive (t : ℝ) : ℝ := ∫ σ in (-(1 / 4) : ℝ)..t, normalizedBump σ
lemma contDiff_bumpPrimitive : ContDiff ℝ ∞ bumpPrimitive :=
  contDiff_integral_from contDiff_normalizedBump _
lemma mollifiedUnitIndicator_eq_integral (t : ℝ) :
    mollifiedUnitIndicator t = ∫ σ in (t - 1 / 2)..(t + 1 / 2), normalizedBump σ := by
  have h1 : mollifiedUnitIndicator t = ∫ τ, (Ico (-(1 / 2) : ℝ) (1 / 2)).indicator
      (fun τ => normalizedBump (t - τ)) τ := by
    rw [mollifiedUnitIndicator, convolution_def]
    refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
    by_cases h : τ ∈ Ico (-(1 / 2) : ℝ) (1 / 2)
    · rw [indicator_of_mem h]
      simp only [indicator_of_mem h]
      simp
    · rw [indicator_of_notMem h]
      simp only [indicator_of_notMem h]
      simp
  rw [h1, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun σ => normalizedBump σ) t]
  congr 1
  ring
lemma mollifiedUnitIndicator_eq_sub (t : ℝ) :
    mollifiedUnitIndicator t = bumpPrimitive (t + 1 / 2) - bumpPrimitive (t - 1 / 2) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable normalizedBump volume a b := fun a b =>
    contDiff_normalizedBump.continuous.intervalIntegrable a b
  rw [mollifiedUnitIndicator_eq_integral, bumpPrimitive, bumpPrimitive,
    intervalIntegral.integral_interval_sub_left (hi _ _) (hi _ _)]
lemma mollifiedUnitIndicator_eq_fun_sub :
    mollifiedUnitIndicator = fun t => bumpPrimitive (t + 1 / 2) - bumpPrimitive (t - 1 / 2) :=
  funext mollifiedUnitIndicator_eq_sub
lemma contDiff_mollifiedUnitIndicator : ContDiff ℝ ∞ mollifiedUnitIndicator := by
  rw [mollifiedUnitIndicator_eq_fun_sub]
  exact (contDiff_bumpPrimitive.comp (by fun_prop)).sub
    (contDiff_bumpPrimitive.comp (by fun_prop))
section Primitive
variable (hn : ExpNegInvIntegralBounds)
include hn
lemma normalizedBump_nonneg (t : ℝ) : 0 ≤ normalizedBump t := by
  rw [normalizedBump_apply]
  exact mul_nonneg (inv_nonneg.mpr (bumpIntegralConst_pos hn).le) (bumpWeight_nonneg hn t)
lemma normalizedBump_eq_zero_of_not_mem {t : ℝ} (h : t ∉ Ioo (-(1 / 4) : ℝ) (1 / 4)) :
    normalizedBump t = 0 := by
  rw [normalizedBump_apply, bumpWeight_eq_zero_of_not_mem hn h, mul_zero]
lemma monotone_bumpPrimitive : Monotone bumpPrimitive := by
  refine monotone_of_deriv_nonneg (contDiff_bumpPrimitive.differentiable (by simp)) fun t => ?_
  have h : deriv bumpPrimitive t = normalizedBump t :=
    (hasDerivAt_integral_from contDiff_normalizedBump.continuous _ t).deriv
  rw [h]
  exact normalizedBump_nonneg hn t
lemma bumpPrimitive_of_le {t : ℝ} (ht : t ≤ -(1 / 4)) : bumpPrimitive t = 0 := by
  have : ∫ σ in (-(1 / 4) : ℝ)..t, normalizedBump σ = ∫ σ in (-(1 / 4) : ℝ)..t, (0 : ℝ) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_ge ht] at hx
    exact normalizedBump_eq_zero_of_not_mem hn fun hh => absurd hh.1 (not_lt.mpr hx.2)
  rw [bumpPrimitive, this]
  simp
lemma bumpPrimitive_quarter : bumpPrimitive (1 / 4) = 1 := by
  rw [bumpPrimitive, normalizedBump_eq, intervalIntegral.integral_const_mul,
    ← bumpIntegralConst_eq_intervalIntegral hn]
  exact inv_mul_cancel₀ (bumpIntegralConst_pos hn).ne'
lemma bumpPrimitive_of_ge {t : ℝ} (ht : 1 / 4 ≤ t) : bumpPrimitive t = 1 := by
  have h1 : ∫ σ in (1 / 4 : ℝ)..t, normalizedBump σ = 0 := by
    have : ∫ σ in (1 / 4 : ℝ)..t, normalizedBump σ = ∫ σ in (1 / 4 : ℝ)..t, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [uIcc_of_le ht] at hx
      exact normalizedBump_eq_zero_of_not_mem hn fun hh => absurd hh.2 (not_lt.mpr hx.1)
    rw [this]
    simp
  have hi : ∀ a b : ℝ, IntervalIntegrable normalizedBump volume a b := fun a b =>
    contDiff_normalizedBump.continuous.intervalIntegrable a b
  have h2 := intervalIntegral.integral_add_adjacent_intervals (hi (-(1 / 4)) (1 / 4)) (hi (1 / 4) t)
  have h3 := bumpPrimitive_quarter hn
  rw [bumpPrimitive] at h3 ⊢
  rw [← h2, h1, add_zero, h3]
lemma bumpPrimitive_mem_Icc (t : ℝ) : bumpPrimitive t ∈ Icc (0 : ℝ) 1 := by
  have hm := monotone_bumpPrimitive hn
  constructor
  · calc (0 : ℝ) = bumpPrimitive (min t (-(1 / 4))) :=
          (bumpPrimitive_of_le hn (min_le_right _ _)).symm
      _ ≤ bumpPrimitive t := hm (min_le_left _ _)
  · calc bumpPrimitive t ≤ bumpPrimitive (max t (1 / 4)) := hm (le_max_left _ _)
      _ = 1 := bumpPrimitive_of_ge hn (le_max_right _ _)
lemma mollifiedUnitIndicator_nonneg (t : ℝ) : 0 ≤ mollifiedUnitIndicator t := by
  rw [mollifiedUnitIndicator_eq_sub, sub_nonneg]
  exact monotone_bumpPrimitive hn (by linarith)
lemma mollifiedUnitIndicator_le_one (t : ℝ) : mollifiedUnitIndicator t ≤ 1 := by
  rw [mollifiedUnitIndicator_eq_sub]
  linarith [(bumpPrimitive_mem_Icc hn (t + 1 / 2)).2, (bumpPrimitive_mem_Icc hn (t - 1 / 2)).1]
lemma mollifiedUnitIndicator_eq_zero_of_le_abs {t : ℝ} (ht : 3 / 4 ≤ |t|) :
    mollifiedUnitIndicator t = 0 := by
  rw [mollifiedUnitIndicator_eq_sub]
  rcases le_abs.mp ht with h | h
  · rw [bumpPrimitive_of_ge hn (by linarith), bumpPrimitive_of_ge hn (by linarith), sub_self]
  · rw [bumpPrimitive_of_le hn (by linarith), bumpPrimitive_of_le hn (by linarith), sub_self]
lemma abs_lt_of_mollifiedUnitIndicator_ne_zero {t : ℝ} (ht : mollifiedUnitIndicator t ≠ 0) :
    |t| < 3 / 4 := by
  by_contra h
  exact ht (mollifiedUnitIndicator_eq_zero_of_le_abs hn (not_lt.mp h))
lemma tsupport_mollifiedUnitIndicator :
    tsupport mollifiedUnitIndicator ⊆ Icc (-(3 / 4) : ℝ) (3 / 4) := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have := abs_lt.mp (abs_lt_of_mollifiedUnitIndicator_ne_zero hn ht)
  exact ⟨this.1.le, this.2.le⟩
lemma tsum_mollifiedUnitIndicator_sub_int (t : ℝ) :
    ∑' l : ℤ, mollifiedUnitIndicator (t - l) = 1 := by
  set m : ℤ := ⌊t + 1 / 2⌋ with hm
  have hm1 : (m : ℝ) ≤ t + 1 / 2 := Int.floor_le _
  have hm2 : t + 1 / 2 < m + 1 := Int.lt_floor_add_one _
  have hzero : ∀ l ∉ ({m - 1, m, m + 1} : Finset ℤ), mollifiedUnitIndicator (t - l) = 0 := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hl
    refine mollifiedUnitIndicator_eq_zero_of_le_abs hn ?_
    rcases lt_or_ge l (m - 1) with h | h
    · have h' : (l : ℝ) ≤ m - 2 := by
        have : l ≤ m - 2 := by omega
        exact_mod_cast this
      exact le_abs.mpr (Or.inl (by linarith))
    · have h' : (m : ℝ) + 2 ≤ l := by
        have : m + 2 ≤ l := by omega
        exact_mod_cast this
      exact le_abs.mpr (Or.inr (by linarith))
  rw [tsum_eq_sum hzero, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp),
    Finset.sum_singleton]
  simp only [mollifiedUnitIndicator_eq_sub]
  push_cast
  have e1 : bumpPrimitive (t - (m - 1) + 1 / 2) = 1 :=
    bumpPrimitive_of_ge hn (by linarith)
  have e2 : bumpPrimitive (t - (m + 1) - 1 / 2) = 0 :=
    bumpPrimitive_of_le hn (by linarith)
  have e3 : t - (m - 1) - 1 / 2 = t - m + 1 / 2 := by ring
  have e4 : t - m - 1 / 2 = t - (m + 1) + 1 / 2 := by ring
  rw [e1, e2, e3, e4]
  ring
lemma encard_support_mollifiedUnitIndicator_le (t : ℝ) :
    (Function.support fun l : ℤ => mollifiedUnitIndicator (t - l)).encard ≤ 2 := by
  set m : ℤ := ⌊t + 3 / 4⌋ with hm
  have hm1 : (m : ℝ) ≤ t + 3 / 4 := Int.floor_le _
  have hsub : (Function.support fun l : ℤ => mollifiedUnitIndicator (t - l)) ⊆ {m - 1, m} := by
    intro l hl
    have h := abs_lt.mp (abs_lt_of_mollifiedUnitIndicator_ne_zero hn hl)
    have h1 : l ≤ m := Int.le_floor.mpr (by linarith [h.1])
    have h2 : m - 2 < l := by
      have : ((m - 2 : ℤ) : ℝ) < l := by
        push_cast
        linarith [h.2]
      exact_mod_cast this
    have : l = m - 1 ∨ l = m := by omega
    simpa using this
  exact (encard_le_encard hsub).trans_eq (encard_pair (by omega))
end Primitive
lemma abs_iteratedDeriv_normalizedBump_le (hn : ExpNegInvIntegralBounds)
    (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r normalizedBump t| ≤
      integralConstBound * (blockConst ^ r * (r.factorial : ℝ) ^ 2) := by
  have hc := inv_nonneg.mpr (bumpIntegralConst_pos hn).le
  rw [normalizedBump_eq, iteratedDeriv_const_mul_field, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul inv_bumpIntegralConst_le (abs_iteratedDeriv_bumpWeight_le hg r t) (abs_nonneg _)
    (by linarith [one_le_integralConstBound])
lemma abs_iteratedDeriv_mollifiedUnitIndicator_le (hn : ExpNegInvIntegralBounds)
    (hg : BumpProfileGevrey) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r mollifiedUnitIndicator t| ≤
      integralConstBound * blockConst ^ r * (r.factorial : ℝ) ^ 2 := by
  have hA : (1 : ℝ) ≤ integralConstBound := one_le_integralConstBound
  cases r with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    rw [abs_of_nonneg (mollifiedUnitIndicator_nonneg hn t)]
    exact (mollifiedUnitIndicator_le_one hn t).trans hA
  | succ r =>
    have hd : ∀ x, iteratedDeriv (r + 1) bumpPrimitive x = iteratedDeriv r normalizedBump x :=
      fun x => congrFun (iteratedDeriv_succ_integral_from contDiff_normalizedBump.continuous _ r) x
    have c₁ : ContDiffAt ℝ ((r + 1 : ℕ) : ℕ∞ω) (fun t : ℝ => bumpPrimitive (t + 1 / 2)) t :=
      ((contDiff_bumpPrimitive.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ => t + 1 / 2)).of_le
        (by exact_mod_cast le_top)).contDiffAt
    have c₂ : ContDiffAt ℝ ((r + 1 : ℕ) : ℕ∞ω) (fun t : ℝ => bumpPrimitive (t - 1 / 2)) t :=
      ((contDiff_bumpPrimitive.comp (by fun_prop : ContDiff ℝ ∞ fun t : ℝ => t - 1 / 2)).of_le
        (by exact_mod_cast le_top)).contDiffAt
    rw [mollifiedUnitIndicator_eq_fun_sub, iteratedDeriv_fun_sub c₁ c₂,
      congrFun (iteratedDeriv_comp_add_const (r + 1) bumpPrimitive (1 / 2 : ℝ)) t,
      congrFun (iteratedDeriv_comp_sub_const (r + 1) bumpPrimitive (1 / 2 : ℝ)) t, hd, hd]
    have h1 := abs_iteratedDeriv_normalizedBump_le hn hg r (t + 1 / 2)
    have h2 := abs_iteratedDeriv_normalizedBump_le hn hg r (t - 1 / 2)
    have hC : blockConst = 18 := blockConst_eq
    have hF : (r.factorial : ℝ) ^ 2 ≤ ((r + 1).factorial : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast Nat.factorial_le (Nat.le_succ r)) 2
    have hB : (0 : ℝ) ≤ blockConst ^ r := by rw [hC]; positivity
    calc |iteratedDeriv r normalizedBump (t + 1 / 2) - iteratedDeriv r normalizedBump (t - 1 / 2)|
        ≤ |iteratedDeriv r normalizedBump (t + 1 / 2)| +
            |iteratedDeriv r normalizedBump (t - 1 / 2)| :=
          abs_sub _ _
      _ ≤ 2 * (integralConstBound * (blockConst ^ r * (r.factorial : ℝ) ^ 2)) := by
          linarith
      _ ≤ 2 * (integralConstBound * (blockConst ^ r * ((r + 1).factorial : ℝ) ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hF hB
          have := mul_le_mul_of_nonneg_left this (by linarith : (0 : ℝ) ≤ integralConstBound)
          linarith
      _ ≤ blockConst * (integralConstBound *
            (blockConst ^ r * ((r + 1).factorial : ℝ) ^ 2)) := by
          refine mul_le_mul_of_nonneg_right (by rw [hC]; norm_num) ?_
          have : (0 : ℝ) ≤ ((r + 1).factorial : ℝ) ^ 2 := by positivity
          positivity
      _ = integralConstBound * blockConst ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2 := by
          ring
def coordCutoff (s : ℝ) : ℝ := 1 - smoothStep (4 * |s| - 3)
lemma productCubeCutoff_eq_prod (y : Fin 4 → ℝ) :
    productCubeCutoff y = ∏ c : Fin 4, coordCutoff (y c) := rfl
lemma coordCutoff_eventuallyEq_of_pos {x : ℝ} (hx : 0 < x) :
    coordCutoff =ᶠ[𝓝 x] fun s => 1 - smoothStep (4 * s - 3) := by
  filter_upwards [lt_mem_nhds hx] with y hy
  simp only [coordCutoff, abs_of_pos hy]
lemma coordCutoff_eventuallyEq_of_neg {x : ℝ} (hx : x < 0) :
    coordCutoff =ᶠ[𝓝 x] fun s => 1 - smoothStep (-4 * s - 3) := by
  filter_upwards [gt_mem_nhds hx] with y hy
  simp only [coordCutoff, abs_of_neg hy]
  congr 2
  ring
section Cube
variable (hn : ExpNegInvIntegralBounds)
include hn
lemma coordCutoff_mem_Icc (s : ℝ) : coordCutoff s ∈ Icc (0 : ℝ) 1 := by
  have h := smoothStep_mem_Icc hn (4 * |s| - 3)
  exact ⟨by simpa [coordCutoff] using h.2, by simpa [coordCutoff] using h.1⟩
lemma coordCutoff_of_abs_le {s : ℝ} (hs : |s| ≤ 3 / 4) : coordCutoff s = 1 := by
  rw [coordCutoff, smoothStep_of_nonpos hn (by linarith), sub_zero]
lemma coordCutoff_of_one_le_abs {s : ℝ} (hs : 1 ≤ |s|) : coordCutoff s = 0 := by
  rw [coordCutoff, smoothStep_of_one_le hn (by linarith), sub_self]
lemma coordCutoff_eventuallyEq_zero : coordCutoff =ᶠ[𝓝 0] fun _ => (1 : ℝ) := by
  filter_upwards [Ioo_mem_nhds (show (-(3 / 4) : ℝ) < 0 by norm_num)
    (show (0 : ℝ) < 3 / 4 by norm_num)] with y hy
  exact coordCutoff_of_abs_le hn (abs_lt.mpr hy).le
lemma contDiff_coordCutoff : ContDiff ℝ ∞ coordCutoff := by
  have hs := contDiff_smoothStep hn
  rw [contDiff_iff_contDiffAt]
  intro x
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · exact ((contDiff_const.sub (hs.comp (by fun_prop :
      ContDiff ℝ ∞ fun s : ℝ => -4 * s - 3))).contDiffAt).congr_of_eventuallyEq
      (coordCutoff_eventuallyEq_of_neg hx)
  · exact contDiffAt_const.congr_of_eventuallyEq (coordCutoff_eventuallyEq_zero hn)
  · exact ((contDiff_const.sub (hs.comp (by fun_prop :
      ContDiff ℝ ∞ fun s : ℝ => 4 * s - 3))).contDiffAt).congr_of_eventuallyEq
      (coordCutoff_eventuallyEq_of_pos hx)
lemma deriv_one_sub_smoothStep_affine (a x : ℝ) :
    deriv (fun s => 1 - smoothStep (a * s - 3)) x =
      -(deriv smoothStep (a * x - 3) * a) := by
  have hd : DifferentiableAt ℝ smoothStep (a * x - 3) :=
    (contDiff_smoothStep hn).differentiable (by simp) _
  have hin : HasDerivAt (fun s : ℝ => a * s - 3) a x := by
    simpa using ((hasDerivAt_id x).const_mul a).sub_const 3
  have h := (hd.hasDerivAt.comp x hin).const_sub 1
  exact h.deriv
lemma abs_deriv_smoothStep_le (hg : BumpProfileGevrey) (u : ℝ) :
    |deriv smoothStep u| ≤ integralConstBound * blockConst := by
  have h := abs_iteratedDeriv_smoothStep_le hn hg 1 u
  simpa [iteratedDeriv_one] using h
lemma abs_deriv_coordCutoff_le (hg : BumpProfileGevrey) (x : ℝ) :
    |deriv coordCutoff x| ≤ 4 * (integralConstBound * blockConst) := by
  have hAC : 0 ≤ integralConstBound * blockConst := by
    have := one_le_integralConstBound
    have := blockConst_eq
    nlinarith
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [(coordCutoff_eventuallyEq_of_neg hx).deriv_eq, deriv_one_sub_smoothStep_affine hn,
      abs_neg, abs_mul]
    have h := abs_deriv_smoothStep_le hn hg (-4 * x - 3)
    rw [show |(-4 : ℝ)| = 4 by norm_num]
    linarith
  · rw [(coordCutoff_eventuallyEq_zero hn).deriv_eq]
    simp only [deriv_const, abs_zero]
    linarith
  · rw [(coordCutoff_eventuallyEq_of_pos hx).deriv_eq, deriv_one_sub_smoothStep_affine hn,
      abs_neg, abs_mul]
    have h := abs_deriv_smoothStep_le hn hg (4 * x - 3)
    rw [show |(4 : ℝ)| = 4 by norm_num]
    linarith
lemma contDiff_productCubeCutoff : ContDiff ℝ ∞ productCubeCutoff := by
  have h : productCubeCutoff = fun y : Fin 4 → ℝ => ∏ c : Fin 4, coordCutoff (y c) := rfl
  rw [h]
  exact contDiff_prod fun c _ =>
    (contDiff_coordCutoff hn).comp (contDiff_apply ℝ ℝ c)
lemma productCubeCutoff_mem_Icc (y : Fin 4 → ℝ) :
    0 ≤ productCubeCutoff y ∧ productCubeCutoff y ≤ 1 := by
  rw [productCubeCutoff_eq_prod]
  exact ⟨Finset.prod_nonneg fun c _ => (coordCutoff_mem_Icc hn _).1,
    Finset.prod_le_one (fun c _ => (coordCutoff_mem_Icc hn _).1)
      fun c _ => (coordCutoff_mem_Icc hn _).2⟩
lemma tsupport_productCubeCutoff :
    tsupport productCubeCutoff ⊆ (univ.pi fun _ : Fin 4 => Icc (-1 : ℝ) 1) := by
  refine closure_minimal (fun y hy => ?_) (isClosed_set_pi fun _ _ => isClosed_Icc)
  intro c _
  by_contra hc
  apply hy
  rw [productCubeCutoff_eq_prod]
  refine Finset.prod_eq_zero (Finset.mem_univ c) (coordCutoff_of_one_le_abs hn ?_)
  by_contra h
  exact hc (abs_le.mp (not_le.mp h).le)
lemma hasCompactSupport_productCubeCutoff : HasCompactSupport productCubeCutoff :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_productCubeCutoff hn)
lemma fderiv_productCubeCutoff_single (y : Fin 4 → ℝ) (c : Fin 4) :
    fderiv ℝ productCubeCutoff y (Pi.single c 1) =
      (∏ j ∈ Finset.univ.erase c, coordCutoff (y j)) * deriv coordCutoff (y c) := by
  have hd : ∀ i : Fin 4, HasFDerivAt (fun z : Fin 4 → ℝ => coordCutoff (z i))
      (deriv coordCutoff (y i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) y := by
    intro i
    have h1 : DifferentiableAt ℝ coordCutoff (y i) :=
      (contDiff_coordCutoff hn).differentiable (by simp) _
    have h2 : HasDerivAt coordCutoff (deriv coordCutoff (y i))
        ((fun z : Fin 4 → ℝ => z i) y) := h1.hasDerivAt
    have hp : HasFDerivAt (𝕜 := ℝ) (fun z : Fin 4 → ℝ => z i)
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) i) y :=
      hasFDerivAt_apply i y
    have h3 := h2.comp_hasFDerivAt y hp
    exact h3
  have hp := HasFDerivAt.finsetProd (u := Finset.univ) fun i _ => hd i
  have hfd : fderiv ℝ productCubeCutoff y = _ := hp.fderiv
  rw [hfd]
  simp only [FunLike.coe_sum, Finset.sum_apply, FunLike.coe_smul,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [Finset.sum_eq_single c]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp
lemma abs_fderiv_productCubeCutoff_single_le (hg : BumpProfileGevrey) (y : Fin 4 → ℝ)
    (c : Fin 4) :
    |fderiv ℝ productCubeCutoff y (Pi.single c 1)| ≤
      4 * (integralConstBound * blockConst) := by
  rw [fderiv_productCubeCutoff_single hn, abs_mul]
  have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase c, coordCutoff (y j) :=
    Finset.prod_nonneg fun j _ => (coordCutoff_mem_Icc hn _).1
  have hP1 : ∏ j ∈ Finset.univ.erase c, coordCutoff (y j) ≤ 1 :=
    Finset.prod_le_one (fun j _ => (coordCutoff_mem_Icc hn _).1)
      fun j _ => (coordCutoff_mem_Icc hn _).2
  rw [abs_of_nonneg hP0]
  calc _ ≤ 1 * |deriv coordCutoff (y c)| :=
        mul_le_mul_of_nonneg_right hP1 (abs_nonneg _)
    _ ≤ _ := by
        rw [one_mul]
        exact abs_deriv_coordCutoff_le hn hg _
lemma sqrt_sum_sq_fderiv_productCubeCutoff_le (hg : BumpProfileGevrey) (y : Fin 4 → ℝ) :
    Real.sqrt (∑ c : Fin 4, (fderiv ℝ productCubeCutoff y (Pi.single c 1)) ^ 2) ≤
      cutoffConst := by
  have hAC : 0 ≤ integralConstBound * blockConst := by
    have := one_le_integralConstBound
    have := blockConst_eq
    nlinarith
  have hN : cutoffConst = 8 * (integralConstBound * blockConst) := by
    simp only [cutoffConst]
    ring
  rw [Real.sqrt_le_iff, hN]
  refine ⟨by positivity, ?_⟩
  calc ∑ c : Fin 4, (fderiv ℝ productCubeCutoff y (Pi.single c 1)) ^ 2
      ≤ ∑ _c : Fin 4, (4 * (integralConstBound * blockConst)) ^ 2 := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_fderiv_productCubeCutoff_single_le hn hg y c) 2
    _ = (8 * (integralConstBound * blockConst)) ^ 2 := by
        simp
        ring
end Cube
theorem smoothBumpsGevreyBounds_of (hn : ExpNegInvIntegralBounds)
    (he : ElementaryInequalities.NormPowerFactorialBounds) :
    SmoothBumpsGevreyBounds := by
  have hg : BumpProfileGevrey := abs_iteratedDeriv_bumpProfile_le he.2.1
  refine ⟨⟨contDiff_bumpProfile, hg⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨contDiff_smoothStep hn, monotone_smoothStep hn,
      fun t ht => smoothStep_of_nonpos hn ht, fun t ht => smoothStep_of_one_le hn ht,
      fun t ht => smoothStep_pos hn ht⟩
  · refine ⟨contDiff_evenSmoothStep hn, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro t
      simp only [evenSmoothStep, abs_neg]
    · exact fun t => smoothStep_mem_Icc hn _
    · intro t ht
      have : |t| ≤ 1 := abs_le.mpr ht
      exact smoothStep_of_nonpos hn (by linarith)
    · intro t ht
      exact smoothStep_pos hn (by linarith)
    · intro t ht
      have h2 : 2 ≤ |t| := by
        by_contra h
        exact ht (abs_lt.mp (not_le.mp h))
      exact smoothStep_of_one_le hn (by linarith)
    · intro t t' h
      exact monotone_smoothStep hn (by linarith)
  · exact ⟨contDiff_mollifiedUnitIndicator,
      fun t => ⟨mollifiedUnitIndicator_nonneg hn t, mollifiedUnitIndicator_le_one hn t⟩,
      tsupport_mollifiedUnitIndicator hn, tsum_mollifiedUnitIndicator_sub_int hn,
      encard_support_mollifiedUnitIndicator_le hn⟩
  · refine ⟨contDiff_productCubeCutoff hn, hasCompactSupport_productCubeCutoff hn,
      productCubeCutoff_mem_Icc hn, ?_, tsupport_productCubeCutoff hn,
      sqrt_sum_sq_fderiv_productCubeCutoff_le hn hg⟩
    intro y hy
    rw [productCubeCutoff_eq_prod]
    exact Finset.prod_eq_one fun c _ =>
      coordCutoff_of_abs_le hn (abs_le.mpr (hy c (mem_univ c)))
  · exact fun r t => ⟨abs_iteratedDeriv_smoothStep_le hn hg r t,
      abs_iteratedDeriv_evenSmoothStep_le hn hg r t,
      abs_iteratedDeriv_mollifiedUnitIndicator_le hn hg r t⟩
end YangMills.Construction.BumpFunctions.GevreyBumps
