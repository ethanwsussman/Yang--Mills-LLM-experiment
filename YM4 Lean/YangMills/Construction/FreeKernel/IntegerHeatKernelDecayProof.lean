import YangMills.Construction.FreeKernel.IntegerHeatKernelDecay
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.FreeKernel.IntegerDecay
open YangMills.Construction.FreeKernel.UnitLattice YangMills.Construction.LatticeKernel MeasureTheory
def fourierIntegrand (T : ℝ) (a a' : ℕ) (n : ℤ) (z : ℂ) : ℂ :=
  Complex.exp (Complex.I * (n : ℂ) * z) * (Complex.exp (Complex.I * z) - 1) ^ a *
    (Complex.exp (-(Complex.I * z)) - 1) ^ a' *
    Complex.exp (-(T : ℂ) * (2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))))
def periodIntegral (T : ℝ) (a a' : ℕ) (n : ℤ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) * ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n (θ : ℂ)
lemma differentiable_fourierIntegrand (T : ℝ) (a a' : ℕ) (n : ℤ) :
    Differentiable ℂ (fourierIntegrand T a a' n) := by
  unfold fourierIntegrand
  fun_prop
lemma continuous_fourierIntegrand_ofReal (T : ℝ) (a a' : ℕ) (n : ℤ) :
    Continuous fun θ : ℝ => fourierIntegrand T a a' n (θ : ℂ) :=
  (differentiable_fourierIntegrand T a a' n).continuous.comp Complex.continuous_ofReal
lemma intervalIntegrable_fourierIntegrand_ofReal (T : ℝ) (a a' : ℕ) (n : ℤ) :
    IntervalIntegrable (fun θ : ℝ => fourierIntegrand T a a' n (θ : ℂ)) volume (-Real.pi) Real.pi :=
  (continuous_fourierIntegrand_ofReal T a a' n).intervalIntegrable _ _
lemma exp_I_mul_add_two_pi (z : ℂ) :
    Complex.exp (Complex.I * (z + 2 * Real.pi)) = Complex.exp (Complex.I * z) := by
  have h : Complex.I * (z + 2 * Real.pi) = Complex.I * z + 2 * Real.pi * Complex.I := by ring
  rw [h, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
lemma exp_neg_I_mul_add_two_pi (z : ℂ) :
    Complex.exp (-(Complex.I * (z + 2 * Real.pi))) = Complex.exp (-(Complex.I * z)) := by
  rw [Complex.exp_neg, exp_I_mul_add_two_pi, ← Complex.exp_neg]
lemma exp_I_int_mul_add_two_pi (n : ℤ) (z : ℂ) :
    Complex.exp (Complex.I * (n : ℂ) * (z + 2 * Real.pi)) =
      Complex.exp (Complex.I * (n : ℂ) * z) := by
  have h : Complex.I * (n : ℂ) * (z + 2 * Real.pi) =
      Complex.I * (n : ℂ) * z + (n : ℂ) * (2 * Real.pi * Complex.I) := by ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
lemma fourierIntegrand_add_two_pi (T : ℝ) (a a' : ℕ) (n : ℤ) (z : ℂ) :
    fourierIntegrand T a a' n (z + 2 * Real.pi) = fourierIntegrand T a a' n z := by
  unfold fourierIntegrand
  rw [exp_I_mul_add_two_pi, exp_neg_I_mul_add_two_pi, exp_I_int_mul_add_two_pi]
lemma integral_fourierIntegrand_shift_im (T : ℝ) (a a' : ℕ) (n : ℤ) (σ : ℝ) :
    ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n (θ : ℂ) =
      ∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n ((θ : ℂ) + σ * Complex.I) := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fourierIntegrand T a a' n)
    ((-Real.pi : ℝ) : ℂ) ((Real.pi : ℂ) + σ * Complex.I)
    (differentiable_fourierIntegrand T a a' n).differentiableOn
  have hre : ((Real.pi : ℂ) + σ * Complex.I).re = Real.pi := by simp
  have him : ((Real.pi : ℂ) + σ * Complex.I).im = σ := by simp
  rw [hre, him, Complex.ofReal_re, Complex.ofReal_im] at h
  have hside : (∫ y : ℝ in (0 : ℝ)..σ, fourierIntegrand T a a' n ((Real.pi : ℂ) + y * Complex.I)) =
      ∫ y : ℝ in (0 : ℝ)..σ, fourierIntegrand T a a' n (((-Real.pi : ℝ) : ℂ) + y * Complex.I) := by
    congr 1
    funext y
    rw [← fourierIntegrand_add_two_pi T a a' n (((-Real.pi : ℝ) : ℂ) + y * Complex.I)]
    congr 1
    push_cast
    ring
  rw [hside] at h
  simp only [Complex.ofReal_zero, zero_mul, add_zero] at h
  rw [add_sub_cancel_right] at h
  exact sub_eq_zero.mp h
lemma fourierIntegrand_zero_zero_ofReal (T : ℝ) (n : ℤ) (θ : ℝ) :
    fourierIntegrand T 0 0 n (θ : ℂ) =
      Complex.exp (Complex.I * (n : ℂ) * (θ : ℂ)) * (Real.exp (-T * laplacianSymbol θ) : ℂ) := by
  have e1 : (θ : ℂ) * Complex.I = Complex.I * θ := mul_comm _ _
  have e2 : -(θ : ℂ) * Complex.I = -(Complex.I * θ) := by ring
  have h2 : (2 : ℂ) * Complex.cos (θ : ℂ) =
      Complex.exp (Complex.I * θ) + Complex.exp (-(Complex.I * θ)) := by
    rw [Complex.two_cos, e1, e2]
  have h3 : ((Real.exp (-T * (2 - 2 * Real.cos θ)) : ℝ) : ℂ) =
      Complex.exp (-(T : ℂ) *
        (2 - Complex.exp (Complex.I * θ) - Complex.exp (-(Complex.I * θ)))) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    linear_combination (T : ℂ) * h2
  unfold fourierIntegrand laplacianSymbol
  rw [h3]
  simp
lemma periodIntegral_zero_zero (T : ℝ) (n : ℤ) : periodIntegral T 0 0 n = discreteHeatKernel T n := by
  unfold periodIntegral discreteHeatKernel
  simp_rw [fourierIntegrand_zero_zero_ofReal]
lemma fourierIntegrand_succ_right (T : ℝ) (a a' : ℕ) (n : ℤ) (z : ℂ) :
    fourierIntegrand T a (a' + 1) n z =
      fourierIntegrand T a a' (n - 1) z - fourierIntegrand T a a' n z := by
  have h : Complex.exp (Complex.I * ((n - 1 : ℤ) : ℂ) * z) =
      Complex.exp (Complex.I * (n : ℂ) * z) * Complex.exp (-(Complex.I * z)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fourierIntegrand
  rw [h, pow_succ]
  ring
lemma fourierIntegrand_succ_left (T : ℝ) (a a' : ℕ) (n : ℤ) (z : ℂ) :
    fourierIntegrand T (a + 1) a' n z =
      fourierIntegrand T a a' (n + 1) z - fourierIntegrand T a a' n z := by
  have h : Complex.exp (Complex.I * ((n + 1 : ℤ) : ℂ) * z) =
      Complex.exp (Complex.I * (n : ℂ) * z) * Complex.exp (Complex.I * z) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold fourierIntegrand
  rw [h, pow_succ]
  ring
lemma periodIntegral_succ_right (T : ℝ) (a a' : ℕ) (n : ℤ) :
    periodIntegral T a (a' + 1) n = periodIntegral T a a' (n - 1) - periodIntegral T a a' n := by
  unfold periodIntegral
  simp_rw [fourierIntegrand_succ_right]
  rw [intervalIntegral.integral_sub (intervalIntegrable_fourierIntegrand_ofReal T a a' (n - 1))
    (intervalIntegrable_fourierIntegrand_ofReal T a a' n)]
  ring
lemma periodIntegral_succ_left (T : ℝ) (a a' : ℕ) (n : ℤ) :
    periodIntegral T (a + 1) a' n = periodIntegral T a a' (n + 1) - periodIntegral T a a' n := by
  unfold periodIntegral
  simp_rw [fourierIntegrand_succ_left]
  rw [intervalIntegral.integral_sub (intervalIntegrable_fourierIntegrand_ofReal T a a' (n + 1))
    (intervalIntegrable_fourierIntegrand_ofReal T a a' n)]
  ring
lemma backwardDiff_iterate_eq_re (T : ℝ) (a' : ℕ) :
    ∀ n, backwardDiff^[a'] (integerHeatKernel T) n = (periodIntegral T 0 a' n).re := by
  induction a' with
  | zero =>
    intro n
    simp [integerHeatKernel, periodIntegral_zero_zero]
  | succ k ih =>
    intro n
    rw [Function.iterate_succ_apply', periodIntegral_succ_right, Complex.sub_re, ← ih, ← ih]
    rfl
lemma forwardDiff_backwardDiff_iterate_eq_re (T : ℝ) (a a' : ℕ) :
    ∀ n, forwardDiff^[a] (backwardDiff^[a'] (integerHeatKernel T)) n =
      (periodIntegral T a a' n).re := by
  induction a with
  | zero =>
    intro n
    exact backwardDiff_iterate_eq_re T a' n
  | succ k ih =>
    intro n
    rw [Function.iterate_succ_apply', periodIntegral_succ_left, Complex.sub_re, ← ih, ← ih]
    rfl
lemma norm_exp_add_mul_I_sub_one_le {τ θ : ℝ} (hτ : |τ| ≤ 1) :
    ‖Complex.exp ((τ : ℂ) + (θ : ℂ) * Complex.I) - 1‖ ≤ 2 * (|θ| + |τ|) := by
  have h1 : Complex.exp ((τ : ℂ) + (θ : ℂ) * Complex.I) - 1 =
      Complex.exp ((θ : ℂ) * Complex.I) * ((Real.exp τ - 1 : ℝ) : ℂ) +
        (Complex.exp (Complex.I * (θ : ℂ)) - 1) := by
    rw [Complex.exp_add, mul_comm Complex.I (θ : ℂ)]
    push_cast
    ring
  have h2 : ‖Complex.exp ((θ : ℂ) * Complex.I)‖ = 1 := Complex.norm_exp_ofReal_mul_I θ
  have h3 : ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ ≤ |θ| := by
    simpa using Real.norm_exp_I_mul_ofReal_sub_one_le (x := θ)
  have h4 := Real.abs_exp_sub_one_le hτ
  have h5 : ‖((Real.exp τ - 1 : ℝ) : ℂ)‖ = |Real.exp τ - 1| := Complex.norm_real _
  rw [h1]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, h2, h5]
  have := abs_nonneg θ
  linarith
lemma heat_exponent_shift_le {T θ s σ : ℝ} (hT : 0 ≤ T) (hσ : |σ| = s) (hs0 : 0 < s)
    (hs1 : s ≤ 1) (hTs : T * s ^ 2 ≤ 1) (hTs' : 1 ≤ (T + 1) * s ^ 2) (hθ : |θ| ≤ Real.pi) :
    -T * (2 - Real.exp (-σ) * Real.cos θ - Real.exp σ * Real.cos θ) ≤
      6 - 4 / Real.pi ^ 2 * (θ / s) ^ 2 := by
  have hσ2 : σ ^ 2 = s ^ 2 := by rw [← hσ, sq_abs]
  set C := Real.cosh σ with hCdef
  have hC : Real.exp σ + Real.exp (-σ) = 2 * C := by
    rw [hCdef, Real.cosh_eq]
    ring
  have hC1 : 1 ≤ C := Real.one_le_cosh σ
  have hC2 : C - 1 ≤ s ^ 2 := by
    have h1 := Real.cosh_le_exp_half_sq σ
    have hs2 : s ^ 2 ≤ 1 := by nlinarith
    have hx : |σ ^ 2 / 2| ≤ 1 := by
      rw [hσ2, abs_of_nonneg (by positivity)]
      linarith
    have h2 := Real.abs_exp_sub_one_le hx
    have h3 := le_abs_self (Real.exp (σ ^ 2 / 2) - 1)
    rw [abs_of_nonneg (a := σ ^ 2 / 2) (by positivity), hσ2] at h2
    rw [hσ2] at h1 h3
    linarith
  have hcos := Real.cos_le_one_sub_mul_cos_sq hθ
  have hθ2 : θ ^ 2 ≤ Real.pi ^ 2 := by
    rw [← sq_abs θ]
    exact pow_le_pow_left₀ (abs_nonneg θ) hθ 2
  set B := 4 / Real.pi ^ 2 * θ ^ 2 with hB
  have hB0 : 0 ≤ B := by positivity
  have hB4 : B ≤ 4 := by
    rw [hB, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    linarith
  have hw : B ≤ 2 - 2 * Real.cos θ := by
    have : 2 / Real.pi ^ 2 * θ ^ 2 * 2 = B := by
      rw [hB]
      ring
    linarith
  have h5 : 4 / Real.pi ^ 2 * (θ / s) ^ 2 ≤ T * B + 4 := by
    have e : 4 / Real.pi ^ 2 * (θ / s) ^ 2 = B * (s ^ 2)⁻¹ := by
      rw [hB, div_pow]
      field_simp
    have h6 : (s ^ 2)⁻¹ ≤ T + 1 := by
      rw [inv_le_iff_one_le_mul₀ (by positivity)]
      linarith
    rw [e]
    have := mul_le_mul_of_nonneg_left h6 hB0
    nlinarith
  have h7 : 2 - 2 * C * Real.cos θ = (2 - 2 * Real.cos θ) * C - 2 * (C - 1) := by ring
  have h8 : 2 - 2 * Real.cos θ ≤ (2 - 2 * Real.cos θ) * C := by
    have : 0 ≤ 2 - 2 * Real.cos θ := hB0.trans hw
    nlinarith
  have h9 : T * (C - 1) ≤ 1 := (mul_le_mul_of_nonneg_left hC2 hT).trans hTs
  have h10 : T * B ≤ T * (2 - 2 * C * Real.cos θ) + 2 := by
    rw [h7]
    have h11 : T * B ≤ T * ((2 - 2 * Real.cos θ) * C) :=
      mul_le_mul_of_nonneg_left (hw.trans h8) hT
    nlinarith
  have h12 : -T * (2 - Real.exp (-σ) * Real.cos θ - Real.exp σ * Real.cos θ) =
      -(T * (2 - 2 * C * Real.cos θ)) := by
    rw [← hC]
    ring
  rw [h12]
  linarith
def gaussianProfile (u : ℝ) : ℝ := (1 + |u|) ^ 3 * Real.exp (-(4 / Real.pi ^ 2) * u ^ 2)
lemma gaussianProfile_nonneg (u : ℝ) : 0 ≤ gaussianProfile u := by
  unfold gaussianProfile
  positivity
lemma continuous_gaussianProfile : Continuous gaussianProfile := by
  unfold gaussianProfile
  fun_prop
lemma integrable_gaussianProfile : Integrable gaussianProfile := by
  have hb : 0 < 2 / Real.pi ^ 2 := by positivity
  refine Integrable.mono' ((integrable_exp_neg_mul_sq hb).const_mul
    (6 * Real.exp (1 + Real.pi ^ 2 / 8))) continuous_gaussianProfile.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_of_nonneg (gaussianProfile_nonneg u)]
  unfold gaussianProfile
  have hx : 0 ≤ 1 + |u| := by positivity
  have h1 : (1 + |u|) ^ 3 ≤ 6 * Real.exp (1 + |u|) := by
    have := Real.pow_div_factorial_le_exp (1 + |u|) hx 3
    have h6 : ((Nat.factorial 3 : ℕ) : ℝ) = 6 := by norm_num [Nat.factorial]
    rw [h6, div_le_iff₀ (by norm_num)] at this
    linarith
  have h2 : |u| ≤ 2 / Real.pi ^ 2 * u ^ 2 + Real.pi ^ 2 / 8 := by
    have e : 2 / Real.pi ^ 2 * u ^ 2 + Real.pi ^ 2 / 8 - |u| =
        2 / Real.pi ^ 2 * (|u| - Real.pi ^ 2 / 4) ^ 2 := by
      rw [← sq_abs u]
      field_simp
      ring
    have : 0 ≤ 2 / Real.pi ^ 2 * (|u| - Real.pi ^ 2 / 4) ^ 2 := by positivity
    linarith
  calc (1 + |u|) ^ 3 * Real.exp (-(4 / Real.pi ^ 2) * u ^ 2)
      ≤ 6 * Real.exp (1 + |u|) * Real.exp (-(4 / Real.pi ^ 2) * u ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = 6 * Real.exp (1 + |u| + -(4 / Real.pi ^ 2) * u ^ 2) := by
        rw [Real.exp_add (1 + |u|)]
        ring
    _ ≤ 6 * Real.exp (1 + Real.pi ^ 2 / 8 + -(2 / Real.pi ^ 2) * u ^ 2) := by
        have e : 4 / Real.pi ^ 2 * u ^ 2 = 2 * (2 / Real.pi ^ 2 * u ^ 2) := by ring
        have : 1 + |u| + -(4 / Real.pi ^ 2) * u ^ 2 ≤
            1 + Real.pi ^ 2 / 8 + -(2 / Real.pi ^ 2) * u ^ 2 := by
          rw [neg_mul, neg_mul, e]
          linarith
        gcongr
    _ = 6 * Real.exp (1 + Real.pi ^ 2 / 8) * Real.exp (-(2 / Real.pi ^ 2) * u ^ 2) := by
        rw [Real.exp_add (1 + Real.pi ^ 2 / 8)]
        ring
lemma norm_fourierIntegrand_shift_le {T s σ θ : ℝ} {a a' : ℕ} {n : ℤ} (hT : 0 ≤ T)
    (hσ : |σ| = s) (hs0 : 0 < s) (hs1 : s ≤ 1) (hTs : T * s ^ 2 ≤ 1)
    (hTs' : 1 ≤ (T + 1) * s ^ 2) (hθ : |θ| ≤ Real.pi) (ha : a + a' ≤ 3)
    (hn : (n : ℝ) * σ = |(n : ℝ)| * s) :
    ‖fourierIntegrand T a a' n ((θ : ℂ) + σ * Complex.I)‖ ≤
      8 * Real.exp 6 * s ^ (a + a') * Real.exp (-(|(n : ℝ)| * s)) * gaussianProfile (θ / s) := by
  set z : ℂ := (θ : ℂ) + σ * Complex.I with hz
  have e1 : Complex.I * z = ((-σ : ℝ) : ℂ) + (θ : ℂ) * Complex.I := by
    rw [hz]
    push_cast
    linear_combination (σ : ℂ) * Complex.I_sq
  have e2 : -(Complex.I * z) = (σ : ℂ) + ((-θ : ℝ) : ℂ) * Complex.I := by
    rw [e1]
    push_cast
    ring
  have b1 : ‖Complex.exp (Complex.I * z) - 1‖ ≤ 2 * (|θ| + s) := by
    rw [e1]
    have := norm_exp_add_mul_I_sub_one_le (τ := -σ) (θ := θ) (by rw [abs_neg, hσ]; exact hs1)
    rwa [abs_neg, hσ] at this
  have b2 : ‖Complex.exp (-(Complex.I * z)) - 1‖ ≤ 2 * (|θ| + s) := by
    rw [e2]
    have := norm_exp_add_mul_I_sub_one_le (τ := σ) (θ := -θ) (by rw [hσ]; exact hs1)
    rwa [abs_neg, hσ] at this
  have b0 : ‖Complex.exp (Complex.I * (n : ℂ) * z)‖ = Real.exp (-(|(n : ℝ)| * s)) := by
    rw [Complex.norm_exp, ← hn]
    congr 1
    have e3 : Complex.I * (n : ℂ) * z = (n : ℂ) * (Complex.I * z) := by ring
    rw [e3, e1]
    simp
  have b3 : ‖Complex.exp (-(T : ℂ) *
      (2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))))‖ ≤
      Real.exp (6 - 4 / Real.pi ^ 2 * (θ / s) ^ 2) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have h := heat_exponent_shift_le hT hσ hs0 hs1 hTs hTs' hθ
    have r1 : (Complex.exp (Complex.I * z)).re = Real.exp (-σ) * Real.cos θ := by
      rw [e1, Complex.exp_re]
      simp
    have r2 : (Complex.exp (-(Complex.I * z))).re = Real.exp σ * Real.cos θ := by
      rw [e2, Complex.exp_re]
      simp
    rw [← Complex.ofReal_neg, Complex.re_ofReal_mul, Complex.sub_re, Complex.sub_re, r1, r2]
    simpa using h
  set u := θ / s with hu
  have hP : 2 * (|θ| + s) = 2 * s * (1 + |u|) := by
    rw [hu, abs_div, abs_of_pos hs0]
    field_simp
    ring
  have hu1 : 1 ≤ 1 + |u| := by
    have := abs_nonneg u
    linarith
  have c1 : ‖Complex.exp (Complex.I * z) - 1‖ ^ a * ‖Complex.exp (-(Complex.I * z)) - 1‖ ^ a' ≤
      (2 * (|θ| + s)) ^ (a + a') := by
    rw [pow_add]
    exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) b1 a)
      (pow_le_pow_left₀ (norm_nonneg _) b2 a') (by positivity) (by positivity)
  have c2 : (2 * (|θ| + s)) ^ (a + a') ≤ 8 * s ^ (a + a') * (1 + |u|) ^ 3 := by
    rw [hP, mul_pow, mul_pow]
    have d1 : (2 : ℝ) ^ (a + a') ≤ 8 := by
      calc (2 : ℝ) ^ (a + a') ≤ 2 ^ 3 := pow_le_pow_right₀ (by norm_num) ha
        _ = 8 := by norm_num
    have d2 : (1 + |u|) ^ (a + a') ≤ (1 + |u|) ^ 3 := pow_le_pow_right₀ hu1 ha
    calc 2 ^ (a + a') * s ^ (a + a') * (1 + |u|) ^ (a + a')
        ≤ 8 * s ^ (a + a') * (1 + |u|) ^ (a + a') := by gcongr
      _ ≤ 8 * s ^ (a + a') * (1 + |u|) ^ 3 := by gcongr
  have hE := Real.exp_pos (-(|(n : ℝ)| * s))
  unfold fourierIntegrand
  rw [norm_mul, norm_mul, norm_mul, norm_pow, norm_pow, b0]
  calc Real.exp (-(|(n : ℝ)| * s)) * ‖Complex.exp (Complex.I * z) - 1‖ ^ a *
        ‖Complex.exp (-(Complex.I * z)) - 1‖ ^ a' * ‖Complex.exp (-(T : ℂ) *
          (2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))))‖
      = Real.exp (-(|(n : ℝ)| * s)) * (‖Complex.exp (Complex.I * z) - 1‖ ^ a *
        ‖Complex.exp (-(Complex.I * z)) - 1‖ ^ a') * ‖Complex.exp (-(T : ℂ) *
          (2 - Complex.exp (Complex.I * z) - Complex.exp (-(Complex.I * z))))‖ := by ring
    _ ≤ Real.exp (-(|(n : ℝ)| * s)) * (8 * s ^ (a + a') * (1 + |u|) ^ 3) *
        Real.exp (6 - 4 / Real.pi ^ 2 * u ^ 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left (c1.trans c2) hE.le) b3 (norm_nonneg _) ?_
        positivity
    _ = 8 * Real.exp 6 * s ^ (a + a') * Real.exp (-(|(n : ℝ)| * s)) * gaussianProfile u := by
        unfold gaussianProfile
        rw [sub_eq_add_neg, Real.exp_add, neg_mul_eq_neg_mul]
        ring_nf
theorem integerHeatKernelDecayBound_holds : IntegerHeatKernelDecayBound := by
  have hK0 : 0 ≤ ∫ u, gaussianProfile u := integral_nonneg gaussianProfile_nonneg
  set K := ∫ u, gaussianProfile u with hK
  refine ⟨8 * Real.exp 6 * K, by positivity, ?_⟩
  intro T hT a a' ha n
  rw [forwardDiff_backwardDiff_iterate_eq_re]
  have hpi := Real.pi_pos
  have hϑ1 : 1 ≤ max T 1 := le_max_right _ _
  have hϑT : T ≤ max T 1 := le_max_left _ _
  have hϑT' : max T 1 ≤ T + 1 := max_le (by linarith) (by linarith)
  set ϑ := max T 1 with hϑ
  have hϑ0 : 0 < ϑ := by linarith
  set s := (Real.sqrt ϑ)⁻¹ with hs
  have hsq : 1 ≤ Real.sqrt ϑ := Real.one_le_sqrt.mpr hϑ1
  have hs0 : 0 < s := inv_pos.mpr (by linarith)
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ hsq
  have hss : s ^ 2 = ϑ⁻¹ := by
    rw [hs, inv_pow, Real.sq_sqrt hϑ0.le]
  have hTs : T * s ^ 2 ≤ 1 := by
    rw [hss, ← div_eq_mul_inv, div_le_one hϑ0]
    exact hϑT
  have hTs' : 1 ≤ (T + 1) * s ^ 2 := by
    rw [hss, ← div_eq_mul_inv, one_le_div hϑ0]
    exact hϑT'
  obtain ⟨σ, hσ, hn⟩ : ∃ σ : ℝ, |σ| = s ∧ (n : ℝ) * σ = |(n : ℝ)| * s := by
    rcases le_total 0 (n : ℝ) with h | h
    · exact ⟨s, abs_of_pos hs0, by rw [abs_of_nonneg h]⟩
    · exact ⟨-s, by rw [abs_neg, abs_of_pos hs0], by rw [abs_of_nonpos h]; ring⟩
  set L := 8 * Real.exp 6 * s ^ (a + a') * Real.exp (-(|(n : ℝ)| * s)) with hL
  have hL0 : 0 ≤ L := by positivity
  have hcont : Continuous fun θ : ℝ => L * gaussianProfile (θ / s) :=
    continuous_const.mul (continuous_gaussianProfile.comp (continuous_id.div_const s))
  have hint : ‖∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n ((θ : ℂ) + σ * Complex.I)‖ ≤
      ∫ θ in (-Real.pi)..Real.pi, L * gaussianProfile (θ / s) := by
    apply intervalIntegral.norm_integral_le_of_norm_le (by linarith)
    · refine Filter.Eventually.of_forall fun θ hθ => ?_
      exact norm_fourierIntegrand_shift_le hT hσ hs0 hs1 hTs hTs'
        (abs_le.mpr ⟨hθ.1.le, hθ.2⟩) ha hn
    · exact hcont.intervalIntegrable _ _
  have hup : ∫ θ in (-Real.pi)..Real.pi, L * gaussianProfile (θ / s) ≤ L * (s * K) := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_of_le (by linarith)]
    refine mul_le_mul_of_nonneg_left ?_ hL0
    calc ∫ θ in Set.Ioc (-Real.pi) Real.pi, gaussianProfile (θ / s)
        ≤ ∫ θ, gaussianProfile (θ / s) :=
          setIntegral_le_integral (integrable_gaussianProfile.comp_div hs0.ne')
            (Filter.Eventually.of_forall fun _ => gaussianProfile_nonneg _)
      _ = s * K := by
          rw [Measure.integral_comp_div gaussianProfile s, abs_of_pos hs0, smul_eq_mul]
  have hfac : ‖(1 / (2 * (Real.pi : ℂ)))‖ ≤ 1 := by
    have h1 : ‖(1 / (2 * (Real.pi : ℂ)))‖ = 1 / (2 * Real.pi) := by
      rw [norm_div, norm_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpi.le]
      simp
    rw [h1, div_le_one (by positivity)]
    linarith [Real.pi_gt_three]
  have hpow : s ^ (a + a') * s = ϑ ^ (-((1 : ℝ) + a + a') / 2) := by
    have e : s = ϑ ^ (-(1 / 2) : ℝ) := by
      rw [hs, Real.sqrt_eq_rpow, Real.rpow_neg hϑ0.le]
    rw [← pow_succ, e, ← Real.rpow_natCast, ← Real.rpow_mul hϑ0.le]
    congr 1
    push_cast
    ring
  have hexp : -(|(n : ℝ)| * s) = -|(n : ℝ)| / Real.sqrt ϑ := by
    rw [hs]
    ring
  calc |(periodIntegral T a a' n).re| ≤ ‖periodIntegral T a a' n‖ := Complex.abs_re_le_norm _
    _ = ‖(1 / (2 * (Real.pi : ℂ)))‖ *
        ‖∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n ((θ : ℂ) + σ * Complex.I)‖ := by
        unfold periodIntegral
        rw [integral_fourierIntegrand_shift_im T a a' n σ, norm_mul]
    _ ≤ 1 * ‖∫ θ in (-Real.pi)..Real.pi, fourierIntegrand T a a' n ((θ : ℂ) + σ * Complex.I)‖ :=
        mul_le_mul_of_nonneg_right hfac (norm_nonneg _)
    _ ≤ L * (s * K) := by
        rw [one_mul]
        exact hint.trans hup
    _ = 8 * Real.exp 6 * K * (s ^ (a + a') * s) * Real.exp (-(|(n : ℝ)| * s)) := by
        rw [hL]
        ring
    _ = 8 * Real.exp 6 * K * ϑ ^ (-((1 : ℝ) + a + a') / 2) *
        Real.exp (-|(n : ℝ)| / Real.sqrt ϑ) := by
        rw [hpow, hexp]
end YangMills.Construction.FreeKernel.IntegerDecay
