import YangMills.Construction.BaseFunctionals.PropertiesOfTheBumpFunctionsProof
import YangMills.Construction.BumpFunctions.SmoothBumpsGevreyBoundsProof
import YangMills.Construction.ColdStepAtMirrorFrames.GapOfANormNearOneProof
import YangMills.Construction.Functions.ExpNegInvBumpProducts
import YangMills.Construction.RealFunctions.GevreyBumpBounds
import Mathlib
set_option autoImplicit false
open Set Filter Topology MeasureTheory
noncomputable section
namespace YangMills.Construction.Bumps.GevreyEstimates
abbrev infOrder : WithTop ℕ∞ := ((⊤ : ℕ∞) : WithTop ℕ∞)
theorem natCast_le_infOrder (r : ℕ) : (r : WithTop ℕ∞) ≤ infOrder := by apply _root_.YangMills.Construction.ColdStepAtMirrorFrames.NormNearOne.natCast_le_smoothTop <;> assumption
theorem natCast_lt_infOrder (r : ℕ) : (r : WithTop ℕ∞) < infOrder := by
  show (r : WithTop ℕ∞) < ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact_mod_cast (ENat.natCast_lt_top r)
theorem contDiff_expNegInv : ContDiff ℝ infOrder expNegInv := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.contDiff_expBump <;> assumption
theorem expNegInv_of_nonpos {t : ℝ} (h : t ≤ 0) : expNegInv t = 0 := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.expBump_of_nonpos <;> assumption
theorem expNegInv_nonneg (t : ℝ) : 0 ≤ expNegInv t := by apply _root_.YangMills.Construction.Mollifiers.BumpProperties.expBump_nonneg <;> assumption
def cexpNegInv (ζ : ℂ) : ℂ := Complex.exp (-1 / ζ)
def openRightHalfPlane : Set ℂ := {ζ | 0 < ζ.re}
theorem isOpen_openRightHalfPlane : IsOpen openRightHalfPlane :=
  isOpen_lt continuous_const Complex.continuous_re
theorem differentiableOn_cexpNegInv :
    DifferentiableOn ℂ cexpNegInv openRightHalfPlane := by
  intro ζ hζ
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp [openRightHalfPlane] at hζ
  have h : DifferentiableAt ℂ (fun z : ℂ => -1 / z) ζ :=
    (differentiableAt_const _).div differentiableAt_id hne
  exact h.cexp.differentiableWithinAt
theorem differentiableOn_iteratedDeriv_cexpNegInv (r : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv r cexpNegInv) openRightHalfPlane := by
  induction r with
  | zero => simpa [iteratedDeriv_zero] using differentiableOn_cexpNegInv
  | succ r ih =>
    rw [iteratedDeriv_succ]
    exact (ih.analyticOnNhd isOpen_openRightHalfPlane).deriv.differentiableOn
theorem ofReal_iteratedDeriv_expNegInv (r : ℕ) : ∀ t : ℝ, 0 < t →
    ((iteratedDeriv r expNegInv t : ℝ) : ℂ) = iteratedDeriv r cexpNegInv (t : ℂ) := by
  induction r with
  | zero =>
    intro t ht
    simp only [iteratedDeriv_zero]
    unfold expNegInv cexpNegInv
    rw [if_pos ht]
    push_cast
    rfl
  | succ r ih =>
    intro t ht
    have hmem : (t : ℂ) ∈ openRightHalfPlane := by simpa [openRightHalfPlane] using ht
    have hG : DifferentiableAt ℂ (iteratedDeriv r cexpNegInv) (t : ℂ) :=
      (differentiableOn_iteratedDeriv_cexpNegInv r).differentiableAt
        (isOpen_openRightHalfPlane.mem_nhds hmem)
    have h1 : HasDerivAt (fun y : ℝ => iteratedDeriv r cexpNegInv (y : ℂ))
        (deriv (iteratedDeriv r cexpNegInv) (t : ℂ)) t := hG.hasDerivAt.comp_ofReal
    have hg : DifferentiableAt ℝ (iteratedDeriv r expNegInv) t :=
      (contDiff_expNegInv.differentiable_iteratedDeriv r (natCast_lt_infOrder r)) t
    have h2 : HasDerivAt (fun y : ℝ => ((iteratedDeriv r expNegInv y : ℝ) : ℂ))
        ((deriv (iteratedDeriv r expNegInv) t : ℝ) : ℂ) t := hg.hasDerivAt.ofReal_comp
    have h3 : (fun y : ℝ => ((iteratedDeriv r expNegInv y : ℝ) : ℂ)) =ᶠ[𝓝 t]
        fun y : ℝ => iteratedDeriv r cexpNegInv (y : ℂ) := by
      filter_upwards [Ioi_mem_nhds ht] with y hy using ih y hy
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact h2.unique (h1.congr_of_eventuallyEq h3)
theorem re_ge_and_norm_le_of_dist_le {t : ℝ} {ζ : ℂ} (h : ‖ζ - t‖ ≤ t / 2) :
    t / 2 ≤ ζ.re - 0 ∧ ‖ζ‖ ≤ 3 * t / 2 := by
  constructor
  · have h1 : |(ζ - t).re| ≤ ‖ζ - t‖ := Complex.abs_re_le_norm _
    have h2 : (ζ - t).re = ζ.re - t := by simp
    rw [h2] at h1
    have := (abs_le.1 (h1.trans h)).1
    linarith
  · have ht : 0 ≤ t := by
      have := (norm_nonneg _).trans h
      linarith
    have h1 : ‖ζ‖ ≤ ‖ζ - t‖ + ‖(t : ℂ)‖ := by simpa using norm_add_le (ζ - t) (t : ℂ)
    have h2 : ‖(t : ℂ)‖ = t := by simp [abs_of_nonneg ht]
    rw [h2] at h1
    linarith
theorem norm_cexpNegInv_le {t : ℝ} (ht : 0 < t) {ζ : ℂ} (h : ‖ζ - t‖ ≤ t / 2) :
    ‖cexpNegInv ζ‖ ≤ Real.exp (-(2 / (9 * t))) := by
  obtain ⟨h1, h2⟩ := re_ge_and_norm_le_of_dist_le h
  have hre : t / 2 ≤ ζ.re := by linarith
  have hre0 : 0 < ζ.re := by linarith
  have hne : ζ ≠ 0 := by
    rintro rfl
    simp at hre0
  have hn : 0 < Complex.normSq ζ := Complex.normSq_pos.2 hne
  unfold cexpNegInv
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.2
  have hval : (-1 / ζ).re = -(ζ.re / Complex.normSq ζ) := by
    simp [neg_div]
  rw [hval, neg_le_neg_iff, div_le_div_iff₀ (by positivity) hn]
  have hsq : Complex.normSq ζ ≤ (3 * t / 2) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  nlinarith [mul_le_mul_of_nonneg_right hre (by positivity : (0 : ℝ) ≤ 9 * t)]
theorem norm_iteratedDeriv_cexpNegInv_le (r : ℕ) {t : ℝ} (ht : 0 < t) :
    ‖iteratedDeriv r cexpNegInv (t : ℂ)‖ ≤
      r.factorial * Real.exp (-(2 / (9 * t))) / (t / 2) ^ r := by
  refine Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le r (by positivity) ?_ ?_
  · refine differentiableOn_cexpNegInv.diffContOnCl_ball ?_
    intro ζ hζ
    have h : ‖ζ - t‖ ≤ t / 2 := by simpa [dist_eq_norm] using hζ
    have := (re_ge_and_norm_le_of_dist_le h).1
    show 0 < ζ.re
    linarith
  · intro ζ hζ
    have h : ‖ζ - t‖ ≤ t / 2 := by
      have : ‖ζ - t‖ = t / 2 := by simpa [dist_eq_norm] using hζ
      exact this.le
    exact norm_cexpNegInv_le ht h
theorem iteratedDeriv_expNegInv_of_nonpos (r : ℕ) {t : ℝ} (ht : t ≤ 0) :
    iteratedDeriv r expNegInv t = 0 := by apply _root_.YangMills.Construction.BumpFunctions.GevreyBumps.iteratedDeriv_bumpProfile_of_nonpos <;> assumption
theorem abs_iteratedDeriv_expNegInv_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r expNegInv t| ≤ (9 : ℝ) ^ r * (r.factorial : ℝ) ^ 2 := by
  rcases le_or_gt t 0 with ht | ht
  · rw [iteratedDeriv_expNegInv_of_nonpos r ht, abs_zero]
    positivity
  · set v : ℝ := 2 / (9 * t) with hv
    have hv0 : 0 < v := by positivity
    have hpow : v ^ r * Real.exp (-v) ≤ r.factorial := by
      have h1 : v ^ r / r.factorial ≤ Real.exp v := Real.pow_div_factorial_le_exp v hv0.le r
      have h2 : v ^ r ≤ Real.exp v * r.factorial :=
        (div_le_iff₀ (by positivity)).1 h1
      calc v ^ r * Real.exp (-v) ≤ (Real.exp v * r.factorial) * Real.exp (-v) :=
            mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
        _ = r.factorial := by
            rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
    have ht2 : t / 2 = (9 * v)⁻¹ := by
      rw [hv]
      field_simp
    have h0 : |iteratedDeriv r expNegInv t| = ‖iteratedDeriv r cexpNegInv (t : ℂ)‖ := by
      rw [← ofReal_iteratedDeriv_expNegInv r t ht, Complex.norm_real, Real.norm_eq_abs]
    rw [h0]
    calc ‖iteratedDeriv r cexpNegInv (t : ℂ)‖
        ≤ r.factorial * Real.exp (-(2 / (9 * t))) / (t / 2) ^ r :=
          norm_iteratedDeriv_cexpNegInv_le r ht
      _ = (9 : ℝ) ^ r * r.factorial * (v ^ r * Real.exp (-v)) := by
          rw [ht2, inv_pow, div_inv_eq_mul, mul_pow, ← hv]
          ring
      _ ≤ (9 : ℝ) ^ r * r.factorial * r.factorial :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (9 : ℝ) ^ r * (r.factorial : ℝ) ^ 2 := by ring
theorem abs_iteratedDeriv_mul_le_of_gevrey {b : ℝ} (hb : 0 ≤ b) {f g : ℝ → ℝ}
    (hf : ContDiff ℝ infOrder f) (hg : ContDiff ℝ infOrder g)
    (hfb : ∀ (r : ℕ) (t : ℝ), |iteratedDeriv r f t| ≤ b ^ r * (r.factorial : ℝ) ^ 2)
    (hgb : ∀ (r : ℕ) (t : ℝ), |iteratedDeriv r g t| ≤ b ^ r * (r.factorial : ℝ) ^ 2)
    (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (fun x => f x * g x) t| ≤ (2 * b) ^ r * (r.factorial : ℝ) ^ 2 := by
  have hfa : ContDiffAt ℝ r f t := (hf.of_le (natCast_le_infOrder r)).contDiffAt
  have hga : ContDiffAt ℝ r g t := (hg.of_le (natCast_le_infOrder r)).contDiffAt
  rw [iteratedDeriv_fun_mul hfa hga]
  calc |∑ i ∈ Finset.range (r + 1),
        (r.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (r - i) g t|
      ≤ ∑ i ∈ Finset.range (r + 1),
        |(r.choose i : ℝ) * iteratedDeriv i f t * iteratedDeriv (r - i) g t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range (r + 1), (r.choose i : ℝ) * (b ^ r * (r.factorial : ℝ) ^ 2) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hir : i ≤ r := Finset.mem_range_succ_iff.1 hi
        rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _ : (0 : ℝ) ≤ (r.choose i : ℝ)),
          mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
        have hfact : (i.factorial : ℝ) * ((r - i).factorial : ℝ) ≤ r.factorial := by
          exact_mod_cast Nat.le_of_dvd (Nat.factorial_pos r) (Nat.factorial_mul_factorial_dvd_factorial hir)
        calc |iteratedDeriv i f t| * |iteratedDeriv (r - i) g t|
            ≤ (b ^ i * (i.factorial : ℝ) ^ 2) * (b ^ (r - i) * ((r - i).factorial : ℝ) ^ 2) :=
              mul_le_mul (hfb i t) (hgb _ t) (abs_nonneg _) (by positivity)
          _ = b ^ r * ((i.factorial : ℝ) * ((r - i).factorial : ℝ)) ^ 2 := by
              have : b ^ r = b ^ i * b ^ (r - i) := by
                rw [← pow_add, Nat.add_sub_cancel' hir]
              rw [this]
              ring
          _ ≤ b ^ r * (r.factorial : ℝ) ^ 2 :=
              mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfact 2) (by positivity)
    _ = (2 * b) ^ r * (r.factorial : ℝ) ^ 2 := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rw [mul_pow]
        ring
def scaledPrimitive (w : ℝ → ℝ) (a c t : ℝ) : ℝ := c⁻¹ * ∫ τ in a..t, w τ
theorem hasDerivAt_scaledPrimitive {w : ℝ → ℝ} (hw : Continuous w) (a c t : ℝ) :
    HasDerivAt (scaledPrimitive w a c) (c⁻¹ * w t) t :=
  ((hw.integral_hasStrictDerivAt a t).hasDerivAt).const_mul c⁻¹
theorem deriv_scaledPrimitive {w : ℝ → ℝ} (hw : Continuous w) (a c : ℝ) :
    deriv (scaledPrimitive w a c) = fun t => c⁻¹ * w t :=
  funext fun t => (hasDerivAt_scaledPrimitive hw a c t).deriv
theorem contDiff_scaledPrimitive {w : ℝ → ℝ} (hw : ContDiff ℝ infOrder w) (a c : ℝ) :
    ContDiff ℝ infOrder (scaledPrimitive w a c) := by
  have hc := hw.continuous
  refine contDiff_infty_iff_deriv.2
    ⟨fun t => (hasDerivAt_scaledPrimitive hc a c t).differentiableAt, ?_⟩
  rw [deriv_scaledPrimitive hc]
  exact contDiff_const.mul hw
theorem iteratedDeriv_succ_scaledPrimitive {w : ℝ → ℝ} (hw : Continuous w) (a c : ℝ) (r : ℕ)
    (t : ℝ) : iteratedDeriv (r + 1) (scaledPrimitive w a c) t = c⁻¹ * iteratedDeriv r w t := by
  rw [iteratedDeriv_succ', deriv_scaledPrimitive hw]
  exact iteratedDeriv_const_mul_field c⁻¹ w
theorem monotone_scaledPrimitive {w : ℝ → ℝ} (hw : Continuous w) (h0 : ∀ t, 0 ≤ w t) (a : ℝ)
    {c : ℝ} (hc : 0 < c) : Monotone (scaledPrimitive w a c) :=
  monotone_of_deriv_nonneg (fun t => (hasDerivAt_scaledPrimitive hw a c t).differentiableAt)
    fun t => by
      rw [(hasDerivAt_scaledPrimitive hw a c t).deriv]
      exact mul_nonneg (inv_nonneg.2 hc.le) (h0 t)
theorem scaledPrimitive_of_le {w : ℝ → ℝ} {a : ℝ} (c : ℝ) (hz : ∀ t, t ≤ a → w t = 0) {t : ℝ}
    (ht : t ≤ a) : scaledPrimitive w a c t = 0 := by
  have h : ∫ τ in a..t, w τ = ∫ τ in a..t, (0 : ℝ) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_ge ht] at hx
      exact hz x hx.2
  unfold scaledPrimitive
  rw [h]
  simp
theorem scaledPrimitive_of_ge {w : ℝ → ℝ} {a b c : ℝ} (hw : Continuous w)
    (hz : ∀ t, b ≤ t → w t = 0) (hc : c = ∫ τ in a..b, w τ) (hc0 : 0 < c) {t : ℝ}
    (ht : b ≤ t) : scaledPrimitive w a c t = 1 := by
  have h1 : ∫ τ in b..t, w τ = ∫ τ in b..t, (0 : ℝ) :=
    intervalIntegral.integral_congr fun x hx => by
      rw [uIcc_of_le ht] at hx
      exact hz x hx.1
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hw.intervalIntegrable (μ := volume) a b) (hw.intervalIntegrable (μ := volume) b t)
  unfold scaledPrimitive
  rw [← h2, h1, intervalIntegral.integral_zero, add_zero, ← hc]
  exact inv_mul_cancel₀ hc0.ne'
theorem mem_Icc_of_monotone_zero_one {P : ℝ → ℝ} {a b : ℝ} (hm : Monotone P)
    (h0 : ∀ t, t ≤ a → P t = 0) (h1 : ∀ t, b ≤ t → P t = 1) (t : ℝ) :
    P t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · rw [← h0 (min t a) (min_le_right _ _)]
    exact hm (min_le_left _ _)
  · rw [← h1 (max t b) (le_max_right _ _)]
    exact hm (le_max_left _ _)
theorem mul_pow_mul_factorial_sq_le_succ {A C : ℝ} (hA : 0 ≤ A) (hC : 1 ≤ C) (r : ℕ) :
    A * (C ^ r * (r.factorial : ℝ) ^ 2) ≤ A * C ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2 := by
  have h1 : C ^ r ≤ C ^ (r + 1) := pow_le_pow_right₀ hC (Nat.le_succ r)
  have h2 : (r.factorial : ℝ) ≤ ((r + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le (Nat.le_succ r)
  have h3 : (r.factorial : ℝ) ^ 2 ≤ ((r + 1).factorial : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h2 2
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h3 (by positivity) (by positivity)) hA
def transitionDensity (τ : ℝ) : ℝ := expNegInv τ * expNegInv (1 - τ)
def bumpDensity (t : ℝ) : ℝ := expNegInv (t + 1 / 4) * expNegInv (1 / 4 - t)
theorem contDiff_expNegInv_const_sub (s : ℝ) : ContDiff ℝ infOrder fun z => expNegInv (s - z) :=
  contDiff_expNegInv.comp (contDiff_const.sub contDiff_id)
theorem contDiff_expNegInv_add_const (s : ℝ) : ContDiff ℝ infOrder fun z => expNegInv (z + s) :=
  contDiff_expNegInv.comp (contDiff_id.add contDiff_const)
theorem contDiff_transitionDensity : ContDiff ℝ infOrder transitionDensity :=
  contDiff_expNegInv.mul (contDiff_expNegInv_const_sub 1)
theorem contDiff_bumpDensity : ContDiff ℝ infOrder bumpDensity :=
  (contDiff_expNegInv_add_const (1 / 4)).mul (contDiff_expNegInv_const_sub (1 / 4))
theorem abs_iteratedDeriv_expNegInv_const_sub (s : ℝ) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (fun z => expNegInv (s - z)) t| ≤ (9 : ℝ) ^ r * (r.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_comp_const_sub]
  simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
  exact abs_iteratedDeriv_expNegInv_le r _
theorem abs_iteratedDeriv_expNegInv_add_const (s : ℝ) (r : ℕ) (t : ℝ) :
    |iteratedDeriv r (fun z => expNegInv (z + s)) t| ≤ (9 : ℝ) ^ r * (r.factorial : ℝ) ^ 2 := by
  rw [iteratedDeriv_comp_add_const]
  exact abs_iteratedDeriv_expNegInv_le r _
theorem twiceGevreyConst_eq : twiceGevreyConst = 2 * 9 := by
  unfold twiceGevreyConst gevreyConst
  rfl
theorem abs_iteratedDeriv_transitionDensity_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r transitionDensity t| ≤ twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  rw [twiceGevreyConst_eq]
  exact abs_iteratedDeriv_mul_le_of_gevrey (by norm_num) contDiff_expNegInv
    (contDiff_expNegInv_const_sub 1) abs_iteratedDeriv_expNegInv_le
    (abs_iteratedDeriv_expNegInv_const_sub 1) r t
theorem abs_iteratedDeriv_bumpDensity_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r bumpDensity t| ≤ twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  rw [twiceGevreyConst_eq]
  exact abs_iteratedDeriv_mul_le_of_gevrey (by norm_num) (contDiff_expNegInv_add_const (1 / 4))
    (contDiff_expNegInv_const_sub (1 / 4)) (abs_iteratedDeriv_expNegInv_add_const (1 / 4))
    (abs_iteratedDeriv_expNegInv_const_sub (1 / 4)) r t
theorem transitionDensity_nonneg (t : ℝ) : 0 ≤ transitionDensity t :=
  mul_nonneg (expNegInv_nonneg _) (expNegInv_nonneg _)
theorem bumpDensity_nonneg (t : ℝ) : 0 ≤ bumpDensity t :=
  mul_nonneg (expNegInv_nonneg _) (expNegInv_nonneg _)
theorem transitionDensity_of_nonpos (t : ℝ) (h : t ≤ 0) : transitionDensity t = 0 := by
  unfold transitionDensity
  rw [expNegInv_of_nonpos h, zero_mul]
theorem transitionDensity_of_one_le (t : ℝ) (h : 1 ≤ t) : transitionDensity t = 0 := by
  unfold transitionDensity
  rw [expNegInv_of_nonpos (by linarith : 1 - t ≤ 0), mul_zero]
theorem bumpDensity_of_le (t : ℝ) (h : t ≤ -(1 / 4)) : bumpDensity t = 0 := by
  unfold bumpDensity
  rw [expNegInv_of_nonpos (by linarith : t + 1 / 4 ≤ 0), zero_mul]
theorem bumpDensity_of_ge (t : ℝ) (h : 1 / 4 ≤ t) : bumpDensity t = 0 := by
  unfold bumpDensity
  rw [expNegInv_of_nonpos (by linarith : 1 / 4 - t ≤ 0), mul_zero]
theorem stepNormalizer_eq : stepNormalizer = ∫ τ in (0 : ℝ)..1, transitionDensity τ := rfl
theorem bumpNormalizer_eq :
    bumpNormalizer = ∫ t in (-(1 / 4) : ℝ)..(1 / 4), bumpDensity t := by
  refine (intervalIntegral.integral_eq_integral_of_support_subset fun x hx => ?_).symm
  have hx' : bumpDensity x ≠ 0 := hx
  constructor
  · by_contra h
    exact hx' (bumpDensity_of_le x (not_lt.1 h))
  · by_contra h
    exact hx' (bumpDensity_of_ge x (not_le.1 h).le)
theorem one_le_normalizerBound : 1 ≤ normalizerBound := le_max_left _ _
theorem inv_stepNormalizer_le : stepNormalizer⁻¹ ≤ normalizerBound :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem inv_bumpNormalizer_le : bumpNormalizer⁻¹ ≤ normalizerBound :=
  (le_max_right _ _).trans (le_max_right _ _)
theorem one_le_twiceGevreyConst : 1 ≤ twiceGevreyConst := by
  rw [twiceGevreyConst_eq]
  norm_num
theorem smoothTransition_eq_scaledPrimitive :
    smoothTransition = scaledPrimitive transitionDensity 0 stepNormalizer := by
  funext t
  unfold smoothTransition scaledPrimitive
  rw [one_div]
  congr 1
  have hint : Integrable transitionDensity :=
    contDiff_transitionDensity.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.intro (K := Icc (0 : ℝ) 1) isCompact_Icc fun x hx => by
        rcases le_or_gt x 0 with h | h
        · exact transitionDensity_of_nonpos x h
        · refine transitionDensity_of_one_le x ?_
          by_contra h1
          exact hx ⟨h.le, (not_le.1 h1).le⟩)
  have h := intervalIntegral.integral_Iic_sub_Iic (a := (0 : ℝ)) (b := t)
    hint.integrableOn hint.integrableOn
  have h0 : ∫ τ in Iic (0 : ℝ), transitionDensity τ = 0 :=
    setIntegral_eq_zero_of_forall_eq_zero fun x hx => transitionDensity_of_nonpos x hx
  rw [h0, sub_zero] at h
  exact h
theorem contDiff_smoothTransition : ContDiff ℝ infOrder smoothTransition := by
  rw [smoothTransition_eq_scaledPrimitive]
  exact contDiff_scaledPrimitive contDiff_transitionDensity _ _
theorem smoothTransition_of_nonpos (t : ℝ) (h : t ≤ 0) : smoothTransition t = 0 := by
  rw [smoothTransition_eq_scaledPrimitive]
  exact scaledPrimitive_of_le _ transitionDensity_of_nonpos h
section Transition
variable (hpos : ∀ t₁ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < ∫ τ in (0 : ℝ)..t₁, transitionDensity τ)
include hpos
theorem stepNormalizer_pos : 0 < stepNormalizer := hpos 1 one_pos le_rfl
theorem monotone_smoothTransition : Monotone smoothTransition := by
  rw [smoothTransition_eq_scaledPrimitive]
  exact monotone_scaledPrimitive contDiff_transitionDensity.continuous transitionDensity_nonneg _
    (stepNormalizer_pos hpos)
theorem smoothTransition_of_one_le (t : ℝ) (h : 1 ≤ t) : smoothTransition t = 1 := by
  rw [smoothTransition_eq_scaledPrimitive]
  exact scaledPrimitive_of_ge contDiff_transitionDensity.continuous transitionDensity_of_one_le
    stepNormalizer_eq (stepNormalizer_pos hpos) h
theorem smoothTransition_pos (t : ℝ) (h : 0 < t) : 0 < smoothTransition t := by
  have h1 : 0 < smoothTransition (min t 1) := by
    rw [smoothTransition_eq_scaledPrimitive]
    exact mul_pos (inv_pos.2 (stepNormalizer_pos hpos))
      (hpos _ (lt_min h one_pos) (min_le_right _ _))
  exact h1.trans_le (monotone_smoothTransition hpos (min_le_left _ _))
theorem smoothTransition_mem_Icc (t : ℝ) : smoothTransition t ∈ Icc (0 : ℝ) 1 :=
  mem_Icc_of_monotone_zero_one (monotone_smoothTransition hpos) smoothTransition_of_nonpos
    (smoothTransition_of_one_le hpos) t
theorem abs_iteratedDeriv_smoothTransition_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r smoothTransition t| ≤
      normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  have hA : 1 ≤ normalizerBound := one_le_normalizerBound
  cases r with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have h := smoothTransition_mem_Icc hpos t
    rw [abs_of_nonneg h.1]
    exact h.2.trans hA
  | succ r =>
    rw [smoothTransition_eq_scaledPrimitive,
      iteratedDeriv_succ_scaledPrimitive contDiff_transitionDensity.continuous,
      abs_mul, abs_of_pos (inv_pos.2 (stepNormalizer_pos hpos))]
    calc stepNormalizer⁻¹ * |iteratedDeriv r transitionDensity t|
        ≤ normalizerBound * (twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2) :=
          mul_le_mul inv_stepNormalizer_le (abs_iteratedDeriv_transitionDensity_le r t)
            (abs_nonneg _) (by linarith)
      _ ≤ _ := mul_pow_mul_factorial_sq_le_succ (by linarith) one_le_twiceGevreyConst r
end Transition
section AbsComp
variable {S : ℝ → ℝ} {δ k : ℝ}
theorem comp_abs_eventuallyEq_of_const_near_zero (hδ : 0 < δ) (hk : ∀ u, u ≤ δ → S u = k)
    {t : ℝ} (ht : 0 ≤ t) : (fun x => S |x|) =ᶠ[𝓝 t] S := by
  rcases ht.lt_or_eq with h | rfl
  · filter_upwards [Ioi_mem_nhds h] with y hy
    rw [abs_of_pos hy]
  · filter_upwards [Ioo_mem_nhds (neg_lt_zero.2 hδ) hδ] with y hy
    rw [hk _ (abs_le.2 ⟨hy.1.le, hy.2.le⟩), hk _ hy.2.le]
theorem contDiff_comp_abs_of_const_near_zero (hS : ContDiff ℝ infOrder S) (hδ : 0 < δ)
    (hk : ∀ u, u ≤ δ → S u = k) : ContDiff ℝ infOrder fun x => S |x| := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases le_or_gt 0 t with h | h
  · exact hS.contDiffAt.congr_of_eventuallyEq (comp_abs_eventuallyEq_of_const_near_zero hδ hk h)
  · have h1 : ContDiff ℝ infOrder fun x => S (-x) := hS.comp contDiff_neg
    refine h1.contDiffAt.congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds h] with y hy
    rw [abs_of_neg hy]
theorem abs_iteratedDeriv_comp_abs_eq (hδ : 0 < δ) (hk : ∀ u, u ≤ δ → S u = k) (r : ℕ)
    (t : ℝ) : |iteratedDeriv r (fun x => S |x|) t| = |iteratedDeriv r S (|t|)| := by
  have hnn : ∀ s : ℝ, 0 ≤ s → iteratedDeriv r (fun x => S |x|) s = iteratedDeriv r S s :=
    fun s hs => (comp_abs_eventuallyEq_of_const_near_zero hδ hk hs).iteratedDeriv_eq r
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h, hnn t h]
  · have h1 := iteratedDeriv_comp_neg r (fun y => S |y|) t
    simp only [abs_neg] at h1
    rw [h1, hnn _ (neg_nonneg.2 h.le), abs_of_neg h]
    simp only [smul_eq_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
end AbsComp
theorem symmetricTransition_eq :
    symmetricTransition = fun x => (fun u => smoothTransition (u - 1)) |x| := rfl
theorem contDiff_shiftedTransition : ContDiff ℝ infOrder fun u => smoothTransition (u - 1) :=
  contDiff_smoothTransition.comp (contDiff_id.sub contDiff_const)
theorem shiftedTransition_of_le (u : ℝ) (h : u ≤ 1) : smoothTransition (u - 1) = 0 :=
  smoothTransition_of_nonpos _ (by linarith)
theorem contDiff_symmetricTransition : ContDiff ℝ infOrder symmetricTransition := by
  rw [symmetricTransition_eq]
  exact contDiff_comp_abs_of_const_near_zero contDiff_shiftedTransition one_pos
    shiftedTransition_of_le
section Symmetric
variable (hpos : ∀ t₁ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < ∫ τ in (0 : ℝ)..t₁, transitionDensity τ)
include hpos
theorem abs_iteratedDeriv_symmetricTransition_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r symmetricTransition t| ≤
      normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  rw [symmetricTransition_eq, abs_iteratedDeriv_comp_abs_eq one_pos shiftedTransition_of_le,
    iteratedDeriv_comp_sub_const]
  exact abs_iteratedDeriv_smoothTransition_le hpos r _
theorem symmetricTransition_properties :
    ContDiff ℝ infOrder symmetricTransition ∧
    (∀ t : ℝ, symmetricTransition (-t) = symmetricTransition t) ∧
    (∀ t : ℝ, symmetricTransition t ∈ Set.Icc (0 : ℝ) 1) ∧
    (∀ t ∈ Set.Icc (-1 : ℝ) 1, symmetricTransition t = 0) ∧
    (∀ t : ℝ, 1 < |t| → 0 < symmetricTransition t) ∧
    (∀ t : ℝ, t ∉ Set.Ioo (-2 : ℝ) 2 → symmetricTransition t = 1) ∧
    ∀ t t' : ℝ, |t| ≤ |t'| → symmetricTransition t ≤ symmetricTransition t' := by
  refine ⟨contDiff_symmetricTransition, fun t => ?_, fun t => smoothTransition_mem_Icc hpos _,
    fun t ht => ?_, fun t ht => smoothTransition_pos hpos _ (by linarith), fun t ht => ?_,
    fun t t' h => ?_⟩
  · unfold symmetricTransition
    rw [abs_neg]
  · exact shiftedTransition_of_le _ (abs_le.2 ht)
  · refine smoothTransition_of_one_le hpos _ ?_
    have h2 : 2 ≤ |t| := by
      by_contra h
      exact ht (abs_lt.1 (not_le.1 h))
    linarith
  · exact monotone_smoothTransition hpos (by linarith)
end Symmetric
def unitBumpPrimitive : ℝ → ℝ := scaledPrimitive bumpDensity (-(1 / 4)) bumpNormalizer
theorem contDiff_unitBumpPrimitive : ContDiff ℝ infOrder unitBumpPrimitive :=
  contDiff_scaledPrimitive contDiff_bumpDensity _ _
theorem mollifiedIndicator_eq_sub (t : ℝ) :
    mollifiedIndicator t = unitBumpPrimitive (t + 1 / 2) - unitBumpPrimitive (t - 1 / 2) := by
  have hcont : Continuous bumpDensity := contDiff_bumpDensity.continuous
  have hnb : unitBump = fun x => bumpNormalizer⁻¹ * bumpDensity x := by
    funext x
    unfold unitBump bumpDensity
    rw [one_div, mul_assoc]
  have h1 : (fun τ : ℝ => (Set.Ico (-(1 / 2) : ℝ) (1 / 2)).indicator (fun _ => (1 : ℝ)) τ *
      unitBump (t - τ)) =
      (Set.Ico (-(1 / 2) : ℝ) (1 / 2)).indicator (fun τ => unitBump (t - τ)) := by
    funext τ
    by_cases h : τ ∈ Set.Ico (-(1 / 2) : ℝ) (1 / 2)
    · rw [indicator_of_mem h, indicator_of_mem h, one_mul]
    · rw [indicator_of_notMem h, indicator_of_notMem h, zero_mul]
  unfold mollifiedIndicator
  rw [h1, integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num),
    intervalIntegral.integral_comp_sub_left (fun x => unitBump x) t, hnb,
    intervalIntegral.integral_const_mul]
  unfold unitBumpPrimitive scaledPrimitive
  rw [← mul_sub, intervalIntegral.integral_interval_sub_left
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  norm_num [sub_eq_add_neg, add_comm]
theorem mollifiedIndicator_eq_fun :
    mollifiedIndicator = fun t => unitBumpPrimitive (t + 1 / 2) - unitBumpPrimitive (t - 1 / 2) :=
  funext mollifiedIndicator_eq_sub
theorem contDiff_mollifiedIndicator : ContDiff ℝ infOrder mollifiedIndicator := by
  rw [mollifiedIndicator_eq_fun]
  exact (contDiff_unitBumpPrimitive.comp (contDiff_id.add contDiff_const)).sub
    (contDiff_unitBumpPrimitive.comp (contDiff_id.sub contDiff_const))
theorem unitBumpPrimitive_of_le (t : ℝ) (h : t ≤ -(1 / 4)) : unitBumpPrimitive t = 0 :=
  scaledPrimitive_of_le _ bumpDensity_of_le h
section Mollified
variable (hpos : 0 < bumpNormalizer)
include hpos
theorem monotone_unitBumpPrimitive : Monotone unitBumpPrimitive :=
  monotone_scaledPrimitive contDiff_bumpDensity.continuous bumpDensity_nonneg _ hpos
theorem unitBumpPrimitive_of_ge (t : ℝ) (h : 1 / 4 ≤ t) : unitBumpPrimitive t = 1 :=
  scaledPrimitive_of_ge contDiff_bumpDensity.continuous bumpDensity_of_ge bumpNormalizer_eq hpos h
theorem unitBumpPrimitive_mem_Icc (t : ℝ) : unitBumpPrimitive t ∈ Icc (0 : ℝ) 1 :=
  mem_Icc_of_monotone_zero_one (monotone_unitBumpPrimitive hpos) unitBumpPrimitive_of_le
    (unitBumpPrimitive_of_ge hpos) t
theorem mollifiedIndicator_nonneg_and_le_one (t : ℝ) :
    0 ≤ mollifiedIndicator t ∧ mollifiedIndicator t ≤ 1 := by
  rw [mollifiedIndicator_eq_sub]
  have h1 := monotone_unitBumpPrimitive hpos (by linarith : t - 1 / 2 ≤ t + 1 / 2)
  have h2 := unitBumpPrimitive_mem_Icc hpos (t + 1 / 2)
  have h3 := unitBumpPrimitive_mem_Icc hpos (t - 1 / 2)
  constructor
  · linarith
  · linarith [h2.2, h3.1]
theorem mollifiedIndicator_eq_zero {t : ℝ} (h : 3 / 4 ≤ |t|) : mollifiedIndicator t = 0 := by
  rw [mollifiedIndicator_eq_sub]
  rcases le_abs'.1 h with h1 | h1
  · rw [unitBumpPrimitive_of_le _ (by linarith), unitBumpPrimitive_of_le _ (by linarith),
      sub_zero]
  · rw [unitBumpPrimitive_of_ge hpos _ (by linarith), unitBumpPrimitive_of_ge hpos _ (by linarith),
      sub_self]
theorem abs_lt_of_mollifiedIndicator_ne_zero {t : ℝ} (h : mollifiedIndicator t ≠ 0) :
    |t| < 3 / 4 := by
  by_contra h1
  exact h (mollifiedIndicator_eq_zero hpos (not_lt.1 h1))
theorem tsupport_mollifiedIndicator_subset :
    tsupport mollifiedIndicator ⊆ Set.Icc (-(3 / 4) : ℝ) (3 / 4) := by
  refine closure_minimal (fun t ht => ?_) isClosed_Icc
  have h := abs_lt.1 (abs_lt_of_mollifiedIndicator_ne_zero hpos ht)
  exact ⟨h.1.le, h.2.le⟩
theorem hasSum_mollifiedIndicator_translates (t : ℝ) :
    HasSum (fun l : ℤ => mollifiedIndicator (t - l)) 1 := by
  obtain ⟨n, hn⟩ := exists_nat_ge (|t| + 1)
  have htl := neg_abs_le t
  have htu := le_abs_self t
  set s : Finset ℤ := (Finset.range (2 * n + 1)).image (fun k : ℕ => (k : ℤ) - n) with hs
  have hzero : ∀ l ∉ s, mollifiedIndicator (t - l) = 0 := by
    intro l hl
    by_contra hne
    have h := abs_lt.1 (abs_lt_of_mollifiedIndicator_ne_zero hpos hne)
    have h1 : (l : ℝ) < n := by linarith [h.1]
    have h2 : (-(n : ℝ)) < l := by linarith [h.2]
    have h1' : l < n := by exact_mod_cast h1
    have h2' : -(n : ℤ) < l := by exact_mod_cast h2
    exact hl (Finset.mem_image.2 ⟨(l + n).toNat, Finset.mem_range.2 (by omega), by omega⟩)
  have hsum : ∑ l ∈ s, mollifiedIndicator (t - l) = 1 := by
    have hinj : Set.InjOn (fun k : ℕ => (k : ℤ) - n) (Finset.range (2 * n + 1) : Set ℕ) := by
      intro a _ b _ hab
      simpa using hab
    rw [hs, Finset.sum_image hinj]
    have hterm : ∀ k : ℕ, mollifiedIndicator (t - (((k : ℤ) - n : ℤ) : ℝ)) =
        unitBumpPrimitive (t - ((k : ℝ) - n) + 1 / 2) -
          unitBumpPrimitive (t - (((k + 1 : ℕ) : ℝ) - n) + 1 / 2) := by
      intro k
      rw [mollifiedIndicator_eq_sub]
      push_cast
      congr 2
      ring
    simp only [hterm]
    rw [Finset.sum_range_sub' (fun k : ℕ => unitBumpPrimitive (t - ((k : ℝ) - n) + 1 / 2))]
    have e1 : (((2 * n + 1 : ℕ) : ℝ)) = 2 * n + 1 := by push_cast; ring
    rw [unitBumpPrimitive_of_ge hpos _ (by push_cast; linarith),
      unitBumpPrimitive_of_le _ (by rw [e1]; linarith)]
    norm_num
  rw [← hsum]
  exact hasSum_sum_of_ne_finset_zero hzero
theorem encard_mollifiedIndicator_translates_le (t : ℝ) :
    {l : ℤ | mollifiedIndicator (t - l) ≠ 0}.encard ≤ 2 := by
  set m : ℤ := ⌊t - 3 / 4⌋ + 1 with hm
  have hsub : {l : ℤ | mollifiedIndicator (t - l) ≠ 0} ⊆ {m, m + 1} := by
    intro l hl
    have h := abs_lt.1 (abs_lt_of_mollifiedIndicator_ne_zero hpos hl)
    have hf1 : ((⌊t - 3 / 4⌋ : ℤ) : ℝ) ≤ t - 3 / 4 := Int.floor_le _
    have hf2 : t - 3 / 4 < ((⌊t - 3 / 4⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
    have h1 : ((⌊t - 3 / 4⌋ : ℤ) : ℝ) < l := by linarith [h.2]
    have h2 : (l : ℝ) < ((⌊t - 3 / 4⌋ : ℤ) : ℝ) + 3 := by linarith [h.1]
    have h1' : ⌊t - 3 / 4⌋ < l := by exact_mod_cast h1
    have h2' : l < ⌊t - 3 / 4⌋ + 3 := by exact_mod_cast h2
    have : l = m ∨ l = m + 1 := by omega
    simpa using this
  exact (Set.encard_le_encard hsub).trans (Set.encard_pair (by omega)).le
theorem abs_iteratedDeriv_mollifiedIndicator_le (r : ℕ) (t : ℝ) :
    |iteratedDeriv r mollifiedIndicator t| ≤
      normalizerBound * twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2 := by
  have hA : 1 ≤ normalizerBound := one_le_normalizerBound
  cases r with
  | zero =>
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, one_pow, mul_one]
    have h := mollifiedIndicator_nonneg_and_le_one hpos t
    rw [abs_of_nonneg h.1]
    exact h.2.trans hA
  | succ r =>
    have hP := contDiff_unitBumpPrimitive
    have hcont := contDiff_bumpDensity.continuous
    have hs1 : ContDiffAt ℝ (r + 1 : ℕ) (fun z => unitBumpPrimitive (z + 1 / 2)) t :=
      ((hP.comp (contDiff_id.add contDiff_const)).of_le (natCast_le_infOrder _)).contDiffAt
    have hs2 : ContDiffAt ℝ (r + 1 : ℕ) (fun z => unitBumpPrimitive (z - 1 / 2)) t :=
      ((hP.comp (contDiff_id.sub contDiff_const)).of_le (natCast_le_infOrder _)).contDiffAt
    have hone : ∀ x : ℝ, |iteratedDeriv (r + 1) unitBumpPrimitive x| ≤
        bumpNormalizer⁻¹ * (twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2) := by
      intro x
      unfold unitBumpPrimitive
      rw [iteratedDeriv_succ_scaledPrimitive hcont, abs_mul, abs_of_pos (inv_pos.2 hpos)]
      exact mul_le_mul_of_nonneg_left (abs_iteratedDeriv_bumpDensity_le r x)
        (inv_nonneg.2 hpos.le)
    rw [mollifiedIndicator_eq_fun, iteratedDeriv_fun_sub hs1 hs2,
      iteratedDeriv_comp_add_const, iteratedDeriv_comp_sub_const]
    have hC : 2 * twiceGevreyConst ^ r ≤ twiceGevreyConst ^ (r + 1) := by
      rw [pow_succ, mul_comm]
      refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (by linarith [one_le_twiceGevreyConst]) r)
      rw [twiceGevreyConst_eq]
      norm_num
    have hf : ((r.factorial : ℝ)) ^ 2 ≤ ((r + 1).factorial : ℝ) ^ 2 := by
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      exact_mod_cast Nat.factorial_le (Nat.le_succ r)
    have hdg : 0 ≤ twiceGevreyConst := by linarith [one_le_twiceGevreyConst]
    calc |iteratedDeriv (r + 1) unitBumpPrimitive (t + 1 / 2) -
          iteratedDeriv (r + 1) unitBumpPrimitive (t - 1 / 2)|
        ≤ |iteratedDeriv (r + 1) unitBumpPrimitive (t + 1 / 2)| +
          |iteratedDeriv (r + 1) unitBumpPrimitive (t - 1 / 2)| := abs_sub _ _
      _ ≤ bumpNormalizer⁻¹ * (twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2) +
          bumpNormalizer⁻¹ * (twiceGevreyConst ^ r * (r.factorial : ℝ) ^ 2) :=
          add_le_add (hone _) (hone _)
      _ = bumpNormalizer⁻¹ * ((2 * twiceGevreyConst ^ r) * (r.factorial : ℝ) ^ 2) := by ring
      _ ≤ normalizerBound * (twiceGevreyConst ^ (r + 1) * ((r + 1).factorial : ℝ) ^ 2) :=
          mul_le_mul inv_bumpNormalizer_le
            (mul_le_mul hC hf (by positivity) (by positivity)) (by positivity) (by linarith)
      _ = _ := by ring
end Mollified
def coordCutoff (s : ℝ) : ℝ := 1 - smoothTransition (4 * |s| - 3)
theorem coordCutoff_eq :
    coordCutoff = fun x => (fun u => 1 - smoothTransition (4 * u - 3)) |x| := rfl
theorem contDiff_scaledTransition :
    ContDiff ℝ infOrder fun u => 1 - smoothTransition (4 * u - 3) :=
  contDiff_const.sub
    (contDiff_smoothTransition.comp ((contDiff_const.mul contDiff_id).sub contDiff_const))
theorem scaledTransition_of_le (u : ℝ) (h : u ≤ 3 / 4) : 1 - smoothTransition (4 * u - 3) = 1 := by
  rw [smoothTransition_of_nonpos _ (by linarith), sub_zero]
theorem contDiff_coordCutoff : ContDiff ℝ infOrder coordCutoff := by
  rw [coordCutoff_eq]
  exact contDiff_comp_abs_of_const_near_zero contDiff_scaledTransition (by norm_num)
    scaledTransition_of_le
theorem contDiff_cubeBump : ContDiff ℝ infOrder cubeBump := by
  have h : cubeBump = fun y => ∏ c, coordCutoff (y c) := rfl
  rw [h]
  exact contDiff_prod fun c _ => contDiff_coordCutoff.comp (contDiff_apply _ _ c)
section Cube
variable (hpos : ∀ t₁ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < ∫ τ in (0 : ℝ)..t₁, transitionDensity τ)
include hpos
theorem coordCutoff_mem_Icc (s : ℝ) : coordCutoff s ∈ Icc (0 : ℝ) 1 := by
  have h := smoothTransition_mem_Icc hpos (4 * |s| - 3)
  unfold coordCutoff
  exact ⟨by linarith [h.2], by linarith [h.1]⟩
theorem coordCutoff_of_one_le {s : ℝ} (h : 1 ≤ |s|) : coordCutoff s = 0 := by
  unfold coordCutoff
  rw [smoothTransition_of_one_le hpos _ (by linarith), sub_self]
theorem abs_deriv_coordCutoff_le (s : ℝ) :
    |deriv coordCutoff s| ≤ 4 * (normalizerBound * twiceGevreyConst) := by
  have h := abs_iteratedDeriv_comp_abs_eq (by norm_num : (0 : ℝ) < 3 / 4)
    scaledTransition_of_le 1 s
  rw [← coordCutoff_eq, iteratedDeriv_one, iteratedDeriv_one] at h
  rw [h]
  set u := |s|
  have hdiff : DifferentiableAt ℝ smoothTransition (4 * u - 3) :=
    (contDiff_smoothTransition.differentiable (by simp)) _
  have hl : HasDerivAt (fun u : ℝ => 4 * u - 3) 4 u := by
    simpa using ((hasDerivAt_id u).const_mul (4 : ℝ)).sub_const 3
  have h1 := (hdiff.hasDerivAt.comp u hl).const_sub 1
  have h2 : deriv (fun u => 1 - smoothTransition (4 * u - 3)) u =
      -(deriv smoothTransition (4 * u - 3) * 4) := h1.deriv
  have hb := abs_iteratedDeriv_smoothTransition_le hpos 1 (4 * u - 3)
  rw [iteratedDeriv_one] at hb
  simp only [pow_one, Nat.factorial_one, Nat.cast_one, one_pow, mul_one] at hb
  rw [h2, abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  linarith
theorem cubeBump_eq_zero {y : Fin 4 → ℝ} {c : Fin 4} (h : 1 ≤ |y c|) : cubeBump y = 0 :=
  Finset.prod_eq_zero (Finset.mem_univ c) (coordCutoff_of_one_le hpos h)
theorem tsupport_cubeBump_subset :
    tsupport cubeBump ⊆ Set.pi Set.univ (fun _ : Fin 4 => Set.Icc (-1 : ℝ) 1) := by
  refine closure_minimal (fun y hy c _ => ?_) (isClosed_set_pi fun _ _ => isClosed_Icc)
  have h : |y c| < 1 := by
    by_contra h1
    exact hy (cubeBump_eq_zero hpos (not_lt.1 h1))
  exact ⟨(abs_lt.1 h).1.le, (abs_lt.1 h).2.le⟩
theorem hasCompactSupport_cubeBump : HasCompactSupport cubeBump :=
  (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_cubeBump_subset hpos)
theorem cubeBump_nonneg_and_le_one (y : Fin 4 → ℝ) : 0 ≤ cubeBump y ∧ cubeBump y ≤ 1 :=
  ⟨Finset.prod_nonneg fun _ _ => (coordCutoff_mem_Icc hpos _).1,
    Finset.prod_le_one (fun _ _ => (coordCutoff_mem_Icc hpos _).1)
      fun _ _ => (coordCutoff_mem_Icc hpos _).2⟩
theorem abs_fderiv_cubeBump_le (y : Fin 4 → ℝ) (c : Fin 4) :
    |fderiv ℝ cubeBump y (Pi.single c 1)| ≤ 4 * (normalizerBound * twiceGevreyConst) := by
  set e : Fin 4 → ℝ := Pi.single c 1 with he
  set K : ℝ := ∏ c' ∈ Finset.univ.erase c, coordCutoff (y c') with hK
  have hline : (fun s : ℝ => cubeBump (y + s • e)) = fun s => coordCutoff (y c + s) * K := by
    funext s
    have h1 : cubeBump (y + s • e) = ∏ c', coordCutoff ((y + s • e) c') := rfl
    rw [h1, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
    congr 1
    · simp [he]
    · refine Finset.prod_congr rfl fun c' hc' => ?_
      have hne : c' ≠ c := Finset.ne_of_mem_erase hc'
      simp [he, Pi.single_eq_of_ne hne]
  have hF : HasFDerivAt cubeBump (fderiv ℝ cubeBump y) y :=
    ((contDiff_cubeBump.differentiable (by simp)) y).hasFDerivAt
  have hl : HasDerivAt (fun s : ℝ => y + s • e) e 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add y
  have h1 : HasDerivAt (fun s : ℝ => cubeBump (y + s • e)) (fderiv ℝ cubeBump y e) 0 :=
    HasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => y + s • e) (0 : ℝ)
      (by simpa using hF : HasFDerivAt cubeBump (fderiv ℝ cubeBump y) (y + (0 : ℝ) • e)) hl
  have hd : HasDerivAt coordCutoff (deriv coordCutoff (y c + 0)) (y c + 0) :=
    ((contDiff_coordCutoff.differentiable (by simp)) _).hasDerivAt
  have h2 : HasDerivAt (fun s : ℝ => coordCutoff (y c + s) * K)
      (deriv coordCutoff (y c + 0) * K) 0 := (hd.comp_const_add (y c) 0).mul_const K
  rw [hline] at h1
  rw [h1.unique h2, abs_mul]
  have hK0 : 0 ≤ K := Finset.prod_nonneg fun _ _ => (coordCutoff_mem_Icc hpos _).1
  have hK1 : K ≤ 1 := Finset.prod_le_one (fun _ _ => (coordCutoff_mem_Icc hpos _).1)
    fun _ _ => (coordCutoff_mem_Icc hpos _).2
  have hb := abs_deriv_coordCutoff_le hpos (y c + 0)
  rw [abs_of_nonneg hK0]
  calc |deriv coordCutoff (y c + 0)| * K ≤ |deriv coordCutoff (y c + 0)| * 1 :=
        mul_le_mul_of_nonneg_left hK1 (abs_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact hb
theorem sqrt_sum_sq_fderiv_cubeBump_le (y : Fin 4 → ℝ) :
    Real.sqrt (∑ c : Fin 4, (fderiv ℝ cubeBump y (Pi.single c 1)) ^ 2) ≤
      cubeBumpGradConst := by
  set M : ℝ := 4 * (normalizerBound * twiceGevreyConst) with hM
  have hc : cubeBumpGradConst = 2 * M := by
    rw [hM]
    unfold cubeBumpGradConst
    ring
  have hM0 : 0 ≤ M := by
    have h1 : (1 : ℝ) ≤ normalizerBound := one_le_normalizerBound
    have h2 : (1 : ℝ) ≤ twiceGevreyConst := one_le_twiceGevreyConst
    rw [hM]
    have : 0 ≤ normalizerBound * twiceGevreyConst :=
      mul_nonneg (by linarith) (by linarith)
    linarith
  refine Real.sqrt_le_iff.2 ⟨by rw [hc]; linarith, ?_⟩
  calc ∑ c : Fin 4, (fderiv ℝ cubeBump y (Pi.single c 1)) ^ 2
      ≤ ∑ _c : Fin 4, M ^ 2 := Finset.sum_le_sum fun c _ => by
        have h := abs_le.1 (abs_fderiv_cubeBump_le hpos y c)
        exact sq_le_sq' h.1 h.2
    _ = 4 * M ^ 2 := by simp
    _ = cubeBumpGradConst ^ 2 := by
        rw [hc]
        ring
end Cube
theorem gevreyBumpBounds_of_expNegInvProductIntegrals
    (hn : ExpNegInvBumps.ExpNegInvProductIntegrals) : GevreyBumpBounds := by
  have hc : (∀ t₁ : ℝ, 0 < t₁ → t₁ ≤ 1 → 0 < ∫ τ in (0 : ℝ)..t₁, transitionDensity τ) ∧
      0 < ∫ t in (-(1 / 4) : ℝ)..(1 / 4), bumpDensity t := by
    obtain ⟨-, -, ⟨h1, h2, -⟩⟩ := hn
    exact ⟨fun t₁ a b => (h1 t₁ a b).1, h2⟩
  obtain ⟨hpos, hb'⟩ := hc
  have hb : 0 < bumpNormalizer := by
    rw [bumpNormalizer_eq]
    exact hb'
  refine ⟨⟨contDiff_expNegInv, abs_iteratedDeriv_expNegInv_le⟩,
    ⟨contDiff_smoothTransition, monotone_smoothTransition hpos, smoothTransition_of_nonpos,
      smoothTransition_of_one_le hpos, smoothTransition_pos hpos⟩,
    symmetricTransition_properties hpos,
    ⟨contDiff_mollifiedIndicator, mollifiedIndicator_nonneg_and_le_one hb,
      tsupport_mollifiedIndicator_subset hb,
      fun t => ⟨hasSum_mollifiedIndicator_translates hb t,
        encard_mollifiedIndicator_translates_le hb t⟩⟩,
    ⟨contDiff_cubeBump, hasCompactSupport_cubeBump hpos, cubeBump_nonneg_and_le_one hpos,
      fun y hy => ?_, tsupport_cubeBump_subset hpos, sqrt_sum_sq_fderiv_cubeBump_le hpos⟩,
    fun r t => ⟨abs_iteratedDeriv_smoothTransition_le hpos r t,
      abs_iteratedDeriv_symmetricTransition_le hpos r t,
      abs_iteratedDeriv_mollifiedIndicator_le hb r t⟩⟩
  refine Finset.prod_eq_one fun c _ => ?_
  exact scaledTransition_of_le _ (abs_le.2 (hy c))
end YangMills.Construction.Bumps.GevreyEstimates
