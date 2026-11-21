import YangMills.Construction.Functions.BoundsOfTheSmearingFilterAndWeightProof
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TriangleKernel
namespace TentFacts
open Real YangMills.Construction.ReflectionPositivity.EnergyMomentum
theorem smearingSeq_neg (n : ℤ) : smearingSeq (-n) = smearingSeq n := by
  unfold smearingSeq
  split_ifs <;> omega
theorem smearingSeq_eq_pow_sum (n : ℤ) : (smearingSeq n : ℂ) =
    1 / 2 * Complex.I ^ n - (-1 : ℂ) ^ n + 1 / 2 * (-Complex.I) ^ n := by
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3) ∧ n = 4 * q + r :=
    ⟨n / 4, n % 4, by omega, by omega⟩
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  have hm : (-1 : ℂ) ≠ 0 := by norm_num
  have hnI : -Complex.I ≠ 0 := neg_ne_zero.mpr hI
  have hfour : ∀ w : ℂ, w ^ (4 : ℕ) = 1 → w ^ (4 * q) = 1 := by
    intro w hw
    rw [zpow_mul, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl, zpow_natCast, hw, one_zpow]
  have e1 := hfour Complex.I Complex.I_pow_four
  have e2 := hfour (-1) (by norm_num)
  have e3 := hfour (-Complex.I) (by rw [neg_pow, Complex.I_pow_four]; norm_num)
  rw [zpow_add₀ hI, zpow_add₀ hm, zpow_add₀ hnI, e1, e2, e3]
  have hII : Complex.I * Complex.I = -1 := Complex.I_mul_I
  rcases hr with rfl | rfl | rfl | rfl
  · have hz : smearingSeq (4 * q + 0) = 0 := by
      unfold smearingSeq
      split_ifs <;> omega
    rw [hz]
    norm_num
  · have hz : smearingSeq (4 * q + 1) = 1 := by
      unfold smearingSeq
      split_ifs <;> omega
    rw [hz]
    simp only [zpow_one, Int.cast_one]
    ring
  · have hz : smearingSeq (4 * q + 2) = -2 := by
      unfold smearingSeq
      split_ifs <;> omega
    rw [hz, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl]
    simp only [zpow_natCast, pow_two, neg_mul_neg, hII]
    norm_num
  · have hz : smearingSeq (4 * q + 3) = 1 := by
      unfold smearingSeq
      split_ifs <;> omega
    rw [hz, show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl]
    simp only [zpow_natCast, pow_succ, pow_zero, one_mul, neg_mul_neg, hII]
    norm_num
theorem abs_smearingSeq_le_two (n : ℤ) : |(smearingSeq n : ℝ)| ≤ 2 := by apply _root_.YangMills.Construction.SmearingFilter.Bounds.abs_smearingSeq_le <;> assumption
theorem tentFunction_eq_circle_norm (x : ℝ) :
    tentFunction x = 8 * max (1 - 4 * ‖(x : AddCircle (2 * π))‖ / π) 0 := by
  have hv : ((toIocMod Real.two_pi_pos (-π) x : ℝ) : AddCircle (2 * π)) = x := by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff]
    exact ⟨-toIocDiv Real.two_pi_pos (-π) x, by rw [toIocMod]; simp⟩
  have hn : ‖(x : AddCircle (2 * π))‖ = |toIocMod Real.two_pi_pos (-π) x| := by
    calc ‖(x : AddCircle (2 * π))‖
        = ‖((toIocMod Real.two_pi_pos (-π) x : ℝ) : AddCircle (2 * π))‖ := by rw [hv]
      _ = |toIocMod Real.two_pi_pos (-π) x| := by
        refine (AddCircle.norm_coe_eq_abs_iff (2 * π) Real.two_pi_pos.ne').2 ?_
        rw [abs_of_pos Real.two_pi_pos]
        have := abs_toIocMod_le_pi x
        linarith
  rw [tentFunction, hn]
theorem continuous_tentFunction : Continuous tentFunction := by
  have h : tentFunction =
      fun x : ℝ => 8 * max (1 - 4 * ‖(x : AddCircle (2 * π))‖ / π) 0 :=
    funext tentFunction_eq_circle_norm
  rw [h]
  fun_prop
theorem tentFunction_zero : tentFunction 0 = 8 := by
  rw [tentFunction_eq_circle_norm]
  simp
theorem tentFunction_nonneg (x : ℝ) : 0 ≤ tentFunction x :=
  isTentFunction_tentFunction.nonneg x
theorem tentFunction_le_eight (x : ℝ) : tentFunction x ≤ 8 := by
  rw [tentFunction_eq_circle_norm]
  have h : 4 * ‖(x : AddCircle (2 * π))‖ / π ≥ 0 := by positivity
  have : max (1 - 4 * ‖(x : AddCircle (2 * π))‖ / π) 0 ≤ 1 :=
    max_le (by linarith) zero_le_one
  linarith
theorem tentFunction_eq_zero_of_le_dist {x : ℝ} (h : π / 4 ≤ distTwoPiInt x) :
    tentFunction x = 0 := by
  rw [tentFunction_eq_circle_norm, ← distTwoPiInt_eq_norm]
  have hpi := Real.pi_pos
  have : 1 ≤ 4 * distTwoPiInt x / π := by
    rw [le_div_iff₀ hpi]
    linarith
  rw [max_eq_right (by linarith)]
  simp
theorem tentFunction_neg (x : ℝ) : tentFunction (-x) = tentFunction x := by
  rw [tentFunction_eq_circle_norm, tentFunction_eq_circle_norm, AddCircle.coe_neg, norm_neg]
theorem tentFunction_of_le_quarter_pi {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ π / 4) :
    tentFunction x = 8 * (1 - 4 * x / π) := by
  have hpi := Real.pi_pos
  have hx : |x| ≤ π := by
    rw [abs_of_nonneg h0]
    linarith
  rw [isTentFunction_tentFunction.formula x hx, abs_of_nonneg h0, max_eq_left]
  have : 4 * x / π ≤ 1 := by
    rw [div_le_one hpi]
    linarith
  linarith
theorem tentFunction_eq_zero_of_quarter_pi_le {x : ℝ} (h1 : π / 4 ≤ x) (h2 : x ≤ π) :
    tentFunction x = 0 := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ x := by linarith
  have hx : |x| ≤ π := by rwa [abs_of_nonneg h0]
  rw [isTentFunction_tentFunction.formula x hx, abs_of_nonneg h0, max_eq_right]
  · simp
  · have : 1 ≤ 4 * x / π := by
      rw [le_div_iff₀ hpi]
      linarith
    linarith
theorem integral_tent_mul (f : ℝ → ℂ) (hf : Continuous f) :
    ∫ x in (-π)..π, (tentFunction x : ℂ) * f x =
      ∫ x in (0 : ℝ)..(π / 4), ((8 * (1 - 4 * x / π) : ℝ) : ℂ) * (f x + f (-x)) := by
  have hpi := Real.pi_pos
  have hT : Continuous fun x : ℝ => (tentFunction x : ℂ) :=
    Complex.continuous_ofReal.comp continuous_tentFunction
  have hF : Continuous fun x : ℝ => (tentFunction x : ℂ) * f x := hT.mul hf
  have hH : Continuous fun x : ℝ => (tentFunction x : ℂ) * (f x + f (-x)) :=
    hT.mul (hf.add (hf.comp continuous_neg))
  have h1 : ∫ x in (-π)..π, (tentFunction x : ℂ) * f x =
      ∫ x in (0 : ℝ)..π, (tentFunction x : ℂ) * (f x + f (-x)) := by
    rw [← intervalIntegral.integral_add_adjacent_intervals (hF.intervalIntegrable (-π) 0)
      (hF.intervalIntegrable 0 π)]
    have h2 : ∫ x in (-π)..0, (tentFunction x : ℂ) * f x =
        ∫ x in (0 : ℝ)..π, (tentFunction x : ℂ) * f (-x) := by
      have := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := π)
        (fun x => (tentFunction x : ℂ) * f x)
      simp only [tentFunction_neg, neg_zero] at this
      exact this.symm
    have hG : Continuous fun x : ℝ => (tentFunction x : ℂ) * f (-x) :=
      hT.mul (hf.comp continuous_neg)
    rw [h2, add_comm, ← intervalIntegral.integral_add (hF.intervalIntegrable 0 π)
      (hG.intervalIntegrable 0 π)]
    refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [mul_add]
  rw [h1, ← intervalIntegral.integral_add_adjacent_intervals (hH.intervalIntegrable 0 (π / 4))
    (hH.intervalIntegrable (π / 4) π)]
  have h3 : ∫ x in (π / 4)..π, (tentFunction x : ℂ) * (f x + f (-x)) = 0 := by
    have : ∫ x in (π / 4)..π, (tentFunction x : ℂ) * (f x + f (-x)) =
        ∫ x in (π / 4)..π, (0 : ℂ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc_of_le (by linarith)] at hx
      simp [tentFunction_eq_zero_of_quarter_pi_le hx.1 hx.2]
    rw [this]
    simp
  rw [h3, add_zero]
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le (by linarith)] at hx
  rw [tentFunction_of_le_quarter_pi hx.1 hx.2]
theorem integral_slope :
    ∫ x in (0 : ℝ)..(π / 4), 16 * (1 - 4 * x / π) = 2 * π := by
  have hpi := Real.pi_ne_zero
  have hF : ∀ x : ℝ, HasDerivAt (fun x : ℝ => 16 * (x - 2 * x ^ 2 / π))
      (16 * (1 - 4 * x / π)) x := by
    intro x
    have h := ((hasDerivAt_id' x).sub ((((hasDerivAt_id' x).pow 2).const_mul 2).div_const π)).const_mul 16
    refine h.congr_deriv ?_
    simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  field_simp
  ring
theorem integral_slope_mul_cos {c : ℝ} (hc : c ≠ 0) :
    ∫ x in (0 : ℝ)..(π / 4), 16 * (1 - 4 * x / π) * Real.cos (c * x) =
      64 / π * ((1 - Real.cos (c * (π / 4))) / c ^ 2) := by
  have hpi := Real.pi_ne_zero
  have hF : ∀ x : ℝ, HasDerivAt
      (fun x : ℝ => 16 * ((1 - 4 * x / π) * (Real.sin (c * x) / c) -
        4 / π * (Real.cos (c * x) / c ^ 2)))
      (16 * (1 - 4 * x / π) * Real.cos (c * x)) x := by
    intro x
    have hl : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have hs := (Real.hasDerivAt_sin (c * x)).comp x hl
    have hco := (Real.hasDerivAt_cos (c * x)).comp x hl
    have hr : HasDerivAt (fun x : ℝ => 1 - 4 * x / π) (-(4 / π)) x := by
      have := (((hasDerivAt_id x).const_mul 4).div_const π).const_sub 1
      simpa using this
    have h := ((hr.mul (hs.div_const c)).sub ((hco.div_const (c ^ 2)).const_mul (4 / π))).const_mul 16
    refine h.congr_deriv ?_
    simp only [Function.comp_apply]
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hF x)
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  have h0 : 1 - 4 * (π / 4) / π = 0 := by
    field_simp
    ring
  simp only [h0, mul_zero, Real.sin_zero, Real.cos_zero]
  field_simp
  ring
def sincSqCoeff (n : ℤ) : ℝ :=
  if n = 0 then 1 else (Real.sin ((n : ℝ) * π / 8) / ((n : ℝ) * π / 8)) ^ 2
theorem cexp_add_cexp_neg (n : ℤ) (x : ℝ) :
    Complex.exp (-(Complex.I * n * x)) + Complex.exp (-(Complex.I * n * ((-x : ℝ) : ℂ))) =
      ((2 * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
  push_cast
  rw [Complex.two_cos, add_comm]
  congr 2 <;> ring
theorem tentFourierCoeff_eq_integral (n : ℤ) :
    tentFourierCoeff n =
      ((1 / (2 * π) * ∫ x in (0 : ℝ)..(π / 4), 16 * (1 - 4 * x / π) * Real.cos ((n : ℝ) * x) : ℝ) :
        ℂ) := by
  have hf : Continuous fun x : ℝ => Complex.exp (-(Complex.I * n * x)) := by fun_prop
  rw [tentFourierCoeff, integral_tent_mul _ hf]
  have : ∫ x in (0 : ℝ)..(π / 4), ((8 * (1 - 4 * x / π) : ℝ) : ℂ) *
      (Complex.exp (-(Complex.I * n * x)) + Complex.exp (-(Complex.I * n * ((-x : ℝ) : ℂ)))) =
      ∫ x in (0 : ℝ)..(π / 4), ((16 * (1 - 4 * x / π) * Real.cos ((n : ℝ) * x) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    rw [cexp_add_cexp_neg, ← Complex.ofReal_mul]
    congr 1
    ring
  rw [this, intervalIntegral.integral_ofReal]
  push_cast
  ring
theorem tentFourierCoeff_eq_sincSq (n : ℤ) : tentFourierCoeff n = (sincSqCoeff n : ℂ) := by
  rw [tentFourierCoeff_eq_integral]
  congr 1
  have hpi := Real.pi_ne_zero
  unfold sincSqCoeff
  split_ifs with hn
  · subst hn
    simp only [Int.cast_zero, zero_mul, Real.cos_zero, mul_one]
    rw [integral_slope]
    field_simp
  · have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    rw [integral_slope_mul_cos hn']
    have hcos : Real.cos ((n : ℝ) * (π / 4)) = 1 - 2 * Real.sin ((n : ℝ) * π / 8) ^ 2 := by
      rw [show (n : ℝ) * (π / 4) = 2 * ((n : ℝ) * π / 8) by ring, Real.cos_two_mul, Real.cos_sq']
      ring
    rw [hcos]
    field_simp
    ring
theorem average_tentFunction : (1 / (2 * π) * ∫ x in (-π)..π, tentFunction x) = 1 := by
  have h : ∫ x in (-π)..π, ((tentFunction x : ℂ) * 1) =
      ∫ x in (0 : ℝ)..(π / 4), ((8 * (1 - 4 * x / π) : ℝ) : ℂ) * (1 + 1) :=
    integral_tent_mul (fun _ => 1) continuous_const
  have h2 : ∫ x in (0 : ℝ)..(π / 4), ((8 * (1 - 4 * x / π) : ℝ) : ℂ) * (1 + 1) =
      ∫ x in (0 : ℝ)..(π / 4), ((16 * (1 - 4 * x / π) : ℝ) : ℂ) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    push_cast
    ring
  simp only [mul_one] at h
  rw [h2, intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal, integral_slope] at h
  rw [Complex.ofReal_injective h]
  have hpi := Real.pi_ne_zero
  field_simp
theorem sincSqCoeff_nonneg (n : ℤ) : 0 ≤ sincSqCoeff n := by
  unfold sincSqCoeff
  split_ifs
  · exact zero_le_one
  · positivity
theorem sincSqCoeff_neg (n : ℤ) : sincSqCoeff (-n) = sincSqCoeff n := by
  unfold sincSqCoeff
  by_cases hn : n = 0
  · simp [hn]
  · have : (((-n : ℤ) : ℝ)) * π / 8 = -((n : ℝ) * π / 8) := by
      push_cast
      ring
    simp only [neg_eq_zero, hn, if_false, this, Real.sin_neg, neg_div_neg_eq]
theorem sincSqCoeff_le {n : ℤ} (hn : n ≠ 0) :
    sincSqCoeff n ≤ 64 / (π * (n : ℝ)) ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
  have hpi := Real.pi_ne_zero
  unfold sincSqCoeff
  rw [if_neg hn, div_pow]
  have hs : Real.sin ((n : ℝ) * π / 8) ^ 2 ≤ 1 := Real.sin_sq_le_one _
  calc Real.sin ((n : ℝ) * π / 8) ^ 2 / ((n : ℝ) * π / 8) ^ 2
      ≤ 1 / ((n : ℝ) * π / 8) ^ 2 := by gcongr
    _ = 64 / (π * (n : ℝ)) ^ 2 := by
      field_simp
      ring
theorem summable_sincSqCoeff : Summable sincSqCoeff := by
  have h2 : Summable fun n : ℤ => 1 / (n : ℝ) ^ 2 :=
    Real.summable_one_div_int_pow.2 (by norm_num)
  have h3 : Summable fun n : ℤ => if n = 0 then (1 : ℝ) else 0 :=
    (hasSum_ite_eq (0 : ℤ) (1 : ℝ)).summable
  refine Summable.of_nonneg_of_le sincSqCoeff_nonneg (fun n => ?_)
    ((h2.mul_left (64 / π ^ 2)).add h3)
  by_cases hn : n = 0
  · subst hn
    simp [sincSqCoeff]
  · rw [if_neg hn, add_zero]
    refine (sincSqCoeff_le hn).trans_eq ?_
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpi := Real.pi_ne_zero
    field_simp
local instance fact_twoPi_pos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩
def tentOnCircle : C(AddCircle (2 * π), ℂ) where
  toFun y := ((8 * max (1 - 4 * ‖y‖ / π) 0 : ℝ) : ℂ)
  continuous_toFun := by fun_prop
theorem tentOnCircle_coe (x : ℝ) :
    tentOnCircle (x : AddCircle (2 * π)) = (tentFunction x : ℂ) := by
  rw [tentFunction_eq_circle_norm]
  rfl
theorem fourier_coe_twoPi (n : ℤ) (x : ℝ) :
    fourier n (x : AddCircle (2 * π)) = Complex.exp (Complex.I * n * x) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [fourier_coe_apply]
  congr 1
  push_cast
  field_simp
theorem fourierCoeff_tentOnCircle (n : ℤ) :
    fourierCoeff tentOnCircle n = tentFourierCoeff n := by
  rw [fourierCoeff_eq_intervalIntegral _ n (-π), show -π + 2 * π = π by ring, tentFourierCoeff,
    Complex.real_smul]
  congr 1
  · push_cast
    rfl
  · refine intervalIntegral.integral_congr fun x _ => ?_
    simp only [fourier_coe_twoPi, tentOnCircle_coe, smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
theorem hasSum_tentFourier (x : ℝ) : HasSum
    (fun n : ℤ => tentFourierCoeff n * Complex.exp (Complex.I * n * x))
    (tentFunction x : ℂ) := by
  have hs : Summable (fourierCoeff tentOnCircle) := by
    have h : Summable fun n : ℤ => (sincSqCoeff n : ℂ) :=
      Complex.ofRealCLM.summable summable_sincSqCoeff
    refine h.congr fun n => ?_
    rw [fourierCoeff_tentOnCircle, tentFourierCoeff_eq_sincSq]
  have h := has_pointwise_sum_fourier_series_of_summable hs (x : AddCircle (2 * π))
  rw [tentOnCircle_coe] at h
  convert h using 2 with n
  rw [fourierCoeff_tentOnCircle, fourier_coe_twoPi, smul_eq_mul]
theorem norm_tentFourier_term (n : ℤ) (x : ℝ) :
    ‖tentFourierCoeff n * Complex.exp (Complex.I * n * x)‖ = sincSqCoeff n := by
  have he : Complex.I * n * x = (((n : ℝ) * x : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [norm_mul, he, Complex.norm_exp_ofReal_mul_I, mul_one, tentFourierCoeff_eq_sincSq,
    Complex.norm_real, Real.norm_of_nonneg (sincSqCoeff_nonneg n)]
end TentFacts
open TentFacts in
theorem seqAndTentProperties_proof : SeqAndTentProperties := by
  have hcoef := tentFourierCoeff_eq_sincSq
  have hb0 : tentFourierCoeff 0 = 1 := by
    rw [hcoef]
    simp [sincSqCoeff]
  have hz0 : smearingSeq 0 = 0 := isSmearingSeq_smearingSeq.zero
  refine ⟨⟨smearingSeq_neg, hz0, smearingSeq_eq_pow_sum⟩, ⟨continuous_tentFunction, ?_, tentFunction_zero,
      fun x h => tentFunction_eq_zero_of_le_dist h, ?_⟩, ⟨hb0, ?_, ?_, ?_, ?_, ?_⟩, ⟨hasSum_tentFourier, ?_, ?_⟩,
      ⟨?_, ?_, ?_, ?_⟩⟩
  · intro x
    rw [tentFunction_zero]
    exact ⟨tentFunction_nonneg x, tentFunction_le_eight x⟩
  · exact average_tentFunction
  · intro n hn
    rw [hcoef, sincSqCoeff, if_neg hn]
  · intro n
    rw [hcoef, hcoef, sincSqCoeff_neg]
  · intro n
    rw [hcoef]
    exact ⟨Complex.ofReal_im _, by simpa using sincSqCoeff_nonneg n⟩
  · intro n hn
    rw [hcoef, Complex.ofReal_re]
    exact sincSqCoeff_le hn
  · simpa only [hcoef, Complex.ofReal_re] using summable_sincSqCoeff
  · intro x
    simpa only [norm_tentFourier_term] using summable_sincSqCoeff
  · have hu := tendstoUniformly_tsum summable_sincSqCoeff
      (f := fun (n : ℤ) (x : ℝ) => tentFourierCoeff n * Complex.exp (Complex.I * n * x))
      (fun n x => (norm_tentFourier_term n x).le)
    have he : (fun x : ℝ => ∑' n : ℤ, tentFourierCoeff n * Complex.exp (Complex.I * n * x)) =
        fun x : ℝ => (tentFunction x : ℂ) := funext fun x => (hasSum_tentFourier x).tsum_eq
    rwa [he] at hu
  · refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      (summable_sincSqCoeff.mul_left 2)
    · rw [hcoef, Complex.ofReal_re]
      exact mul_nonneg (abs_nonneg _) (sincSqCoeff_nonneg n)
    · rw [hcoef, Complex.ofReal_re]
      exact mul_le_mul_of_nonneg_right (abs_smearingSeq_le_two n) (sincSqCoeff_nonneg n)
  · intro n
    rw [hcoef]
    simp
  · intro n
    rw [smearingSeq_neg, hcoef, hcoef, sincSqCoeff_neg]
  · rw [hz0]
    simp
end YangMills.Construction.TriangleKernel
