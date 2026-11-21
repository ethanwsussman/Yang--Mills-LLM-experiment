import YangMills.Construction.EnergyMomentum.ArcoshCurveChord
import Mathlib
set_option autoImplicit false
open Filter Set Topology
noncomputable section
namespace YangMills.Construction.EnergyMomentum.ArcoshCurve
theorem arsinh_one_eq_log : Real.arsinh 1 = Real.log (1 + Real.sqrt 2) := by
  rw [Real.arsinh]
  norm_num
theorem hasDerivAt_arsinh_sin (x : ℝ) :
    HasDerivAt (fun y => Real.arsinh (Real.sin y))
      (Real.cos x / Real.sqrt (1 + Real.sin x ^ 2)) x := by
  have h := (Real.hasDerivAt_sin x).arsinh
  have e : (Real.sqrt (1 + Real.sin x ^ 2))⁻¹ • Real.cos x
      = Real.cos x / Real.sqrt (1 + Real.sin x ^ 2) := by
    rw [smul_eq_mul, div_eq_inv_mul]
  rw [e] at h
  exact h
theorem deriv_arsinh_sin_strictAntiOn :
    StrictAntiOn (deriv fun y => Real.arsinh (Real.sin y))
      (interior (Icc 0 (Real.pi / 2))) := by
  rw [interior_Icc]
  intro a ha b hb hab
  rw [(hasDerivAt_arsinh_sin a).deriv, (hasDerivAt_arsinh_sin b).deriv]
  have hpi := Real.pi_pos
  have hcb : 0 < Real.cos b :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [hb.1], hb.2⟩
  have hcab : Real.cos b < Real.cos a :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two ha.1.le hb.2.le hab
  have hsa : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha.1.le (by linarith [ha.2])
  have hsab : Real.sin a ≤ Real.sin b :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ha.1]) hb.2.le hab.le
  have hsqrt : Real.sqrt (1 + Real.sin a ^ 2) ≤ Real.sqrt (1 + Real.sin b ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hpos : 0 < Real.sqrt (1 + Real.sin a ^ 2) := by positivity
  calc Real.cos b / Real.sqrt (1 + Real.sin b ^ 2)
      ≤ Real.cos b / Real.sqrt (1 + Real.sin a ^ 2) :=
        div_le_div_of_nonneg_left hcb.le hpos hsqrt
    _ < Real.cos a / Real.sqrt (1 + Real.sin a ^ 2) :=
        div_lt_div_of_pos_right hcab hpos
theorem strictConcaveOn_arsinh_sin :
    StrictConcaveOn ℝ (Icc 0 (Real.pi / 2)) fun y => Real.arsinh (Real.sin y) := by
  apply StrictAntiOn.strictConcaveOn_of_deriv (convex_Icc _ _)
  · exact (Real.continuous_arsinh.comp Real.continuous_sin).continuousOn
  · exact deriv_arsinh_sin_strictAntiOn
theorem chord_lt_arsinh_sin {x : ℝ} (hx0 : 0 < x) (hx1 : x < Real.pi / 2) :
    2 * x / Real.pi * Real.log (1 + Real.sqrt 2) < Real.arsinh (Real.sin x) := by
  have hpi := Real.pi_pos
  have hw0 : 0 < 2 * x / Real.pi := by positivity
  have hw1 : 0 < 1 - 2 * x / Real.pi := by
    rw [sub_pos, div_lt_one hpi]
    linarith
  have hconc := strictConcaveOn_arsinh_sin.2
    (show (0 : ℝ) ∈ Icc 0 (Real.pi / 2) from ⟨le_rfl, by linarith⟩)
    (show Real.pi / 2 ∈ Icc 0 (Real.pi / 2) from ⟨by linarith, le_rfl⟩)
    (ne_of_lt (by linarith)) hw1 hw0 (by ring)
  have hcomb : (1 - 2 * x / Real.pi) • (0 : ℝ) + (2 * x / Real.pi) • (Real.pi / 2) = x := by
    simp only [smul_eq_mul]
    field_simp
    ring
  rw [hcomb] at hconc
  simpa [Real.sin_pi_div_two, arsinh_one_eq_log] using hconc
theorem chord_le_arsinh_sin {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ Real.pi / 2) :
    2 * x / Real.pi * Real.log (1 + Real.sqrt 2) ≤ Real.arsinh (Real.sin x) ∧
    (2 * x / Real.pi * Real.log (1 + Real.sqrt 2) = Real.arsinh (Real.sin x) ↔
      x = 0 ∨ x = Real.pi / 2) := by
  rcases hx0.eq_or_lt with rfl | hx0'
  · simp
  rcases hx1.eq_or_lt with rfl | hx1'
  · have e : 2 * (Real.pi / 2) / Real.pi = 1 := by field_simp
    simp [e, arsinh_one_eq_log]
  have hlt := chord_lt_arsinh_sin hx0' hx1'
  refine ⟨hlt.le, ?_, ?_⟩
  · exact fun h => absurd h hlt.ne
  · rintro (h | h) <;> linarith
theorem cos_eq_one_sub_two_sin_half_sq (p : ℝ) :
    Real.cos p = 1 - 2 * Real.sin (p / 2) ^ 2 := by
  have h := Real.cos_two_mul (p / 2)
  rw [show 2 * (p / 2) = p by ring] at h
  nlinarith [Real.sin_sq_add_cos_sq (p / 2)]
theorem arcosh_two_sub_cos (p : ℝ) :
    Real.arcosh (2 - Real.cos p) = 2 * Real.arsinh |Real.sin (p / 2)| := by
  have hy : 0 ≤ Real.arsinh |Real.sin (p / 2)| := Real.arsinh_nonneg_iff.2 (abs_nonneg _)
  have hc : Real.cosh (2 * Real.arsinh |Real.sin (p / 2)|) = 2 - Real.cos p := by
    rw [Real.cosh_two_mul, Real.cosh_sq, Real.sinh_arsinh, sq_abs,
      cos_eq_one_sub_two_sin_half_sq p]
    ring
  rw [← hc, Real.arcosh_cosh (by linarith)]
theorem abs_sin_half_eq {p : ℝ} (hp : p ∈ Icc (-Real.pi) Real.pi) :
    |Real.sin (p / 2)| = Real.sin (|p| / 2) := by
  have hpi := Real.pi_pos
  rcases le_total 0 p with h | h
  · rw [abs_of_nonneg h, abs_of_nonneg]
    exact Real.sin_nonneg_of_nonneg_of_le_pi (by linarith) (by linarith [hp.2])
  · rw [abs_of_nonpos h, abs_of_nonpos, neg_div, Real.sin_neg]
    exact Real.sin_nonpos_of_nonpos_of_neg_pi_le (by linarith) (by linarith [hp.1])
theorem boundOnInterval_holds : BoundOnInterval := by
  intro p hp
  have hpi := Real.pi_pos
  have habs : |p| ≤ Real.pi := abs_le.2 hp
  have hx0 : 0 ≤ |p| / 2 := by positivity
  have hx1 : |p| / 2 ≤ Real.pi / 2 := by linarith
  have hk : chordSlopeConstant * |p|
      = 2 * (2 * (|p| / 2) / Real.pi * Real.log (1 + Real.sqrt 2)) := by
    unfold chordSlopeConstant
    ring
  obtain ⟨hle, heq⟩ := chord_le_arsinh_sin hx0 hx1
  refine ⟨arcosh_two_sub_cos p, ?_, ?_⟩
  · rw [abs_sin_half_eq hp, hk]
    linarith
  · rw [abs_sin_half_eq hp, hk]
    constructor
    · intro h
      have h' := heq.1 (by linarith)
      rcases h' with h' | h'
      · have : p = 0 := abs_eq_zero.1 (by linarith)
        simp [this]
      · have h2 : |p| = Real.pi := by linarith
        rcases abs_choice p with h3 | h3
        · have : p = Real.pi := by rw [← h2, h3]
          simp [this]
        · have : p = -Real.pi := by linarith
          simp [this]
    · intro h
      have h' : |p| / 2 = 0 ∨ |p| / 2 = Real.pi / 2 := by
        simp only [mem_insert_iff, mem_singleton_iff] at h
        rcases h with rfl | rfl | rfl
        · simp
        · right
          rw [abs_of_pos hpi]
        · right
          rw [abs_neg, abs_of_pos hpi]
      have := heq.2 h'
      linarith
theorem norm_one_sub_exp_I_mul_sq (p : ℝ) :
    ‖1 - Complex.exp (Complex.I * (p : ℂ))‖ ^ 2 = 2 - 2 * Real.cos p := by
  rw [mul_comm, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq p]
theorem conditionsEquiv_holds : ConditionsEquiv := by
  intro t ht p hp
  intro E ζ
  have ht0 := ht.1
  have ht1 := ht.2
  have hE0 : 0 ≤ E := neg_nonneg.2 (Real.log_nonpos ht0.le ht1)
  have hexpneg : Real.exp (-E) = t := by
    simp only [E, neg_neg]
    exact Real.exp_log ht0
  have hexp : Real.exp E = t⁻¹ := by
    simp only [E]
    rw [Real.exp_neg, Real.exp_log ht0]
  have hcosh : 2 * t * Real.cosh E = 1 + t ^ 2 := by
    rw [Real.cosh_eq, hexp, hexpneg]
    field_simp
  have hnorm : ‖1 - ζ‖ ^ 2 = 2 - 2 * Real.cos p := norm_one_sub_exp_I_mul_sq p
  have hcosp := cos_eq_one_sub_two_sin_half_sq p
  have hcoshE : Real.cosh E = 1 + 2 * Real.sinh (E / 2) ^ 2 := by
    have h := Real.cosh_two_mul (E / 2)
    rw [show 2 * (E / 2) = E by ring, Real.cosh_sq] at h
    linarith
  have hsh : 0 ≤ Real.sinh (E / 2) := Real.sinh_nonneg_iff.2 (by linarith)
  have hAC : (1 - t) ^ 2 ≥ t * ‖1 - ζ‖ ^ 2 ↔ Real.cosh E + Real.cos p ≥ 2 := by
    rw [hnorm]
    have key : (1 - t) ^ 2 - t * (2 - 2 * Real.cos p)
        = 2 * t * (Real.cosh E + Real.cos p - 2) := by
      linear_combination -hcosh
    have h2t : 0 < 2 * t := by positivity
    constructor
    · intro h
      have h' : 0 ≤ 2 * t * (Real.cosh E + Real.cos p - 2) := by linarith
      have := (mul_nonneg_iff_of_pos_left h2t).1 h'
      linarith
    · intro h
      have h' : 0 ≤ 2 * t * (Real.cosh E + Real.cos p - 2) :=
        mul_nonneg h2t.le (by linarith)
      linarith
  have hBC : Real.sinh (E / 2) ≥ |Real.sin (p / 2)| ↔ Real.cosh E + Real.cos p ≥ 2 := by
    have hsq := pow_le_pow_iff_left₀ (abs_nonneg (Real.sin (p / 2))) hsh two_ne_zero
    rw [sq_abs] at hsq
    rw [ge_iff_le, ← hsq]
    constructor
    · intro h
      linarith
    · intro h
      linarith
  have hCD : Real.cosh E + Real.cos p ≥ 2 ↔ E ≥ Real.arcosh (2 - Real.cos p) := by
    have hpos : 0 < 2 - Real.cos p := by linarith [Real.cos_le_one p]
    have h := Real.arcosh_le_arcosh hpos (Real.cosh_pos E)
    rw [Real.arcosh_cosh hE0] at h
    show 2 ≤ Real.cosh E + Real.cos p ↔ Real.arcosh (2 - Real.cos p) ≤ E
    rw [h]
    constructor
    · intro h'
      linarith
    · intro h'
      linarith
  have hDK : E ≥ Real.arcosh (2 - Real.cos p) → E ≥ chordSlopeConstant * |p| := by
    intro h
    obtain ⟨ha, hb, -⟩ := boundOnInterval_holds p ⟨hp.1.le, hp.2⟩
    rw [ha] at h
    exact le_trans hb h
  exact ⟨hE0, hAC.trans hBC.symm, hBC, hCD, fun h => hDK (hCD.1 (hAC.1 h)),
    fun h => hDK (hCD.1 (hBC.1 h)), fun h => hDK (hCD.1 h), hDK⟩
theorem tendsto_arsinh_sin_div_self :
    Tendsto (fun x : ℝ => Real.arsinh (Real.sin x) / x) (𝓝[≠] 0) (𝓝 1) := by
  have h := hasDerivAt_iff_tendsto_slope.1 (hasDerivAt_arsinh_sin 0)
  have e : Real.cos 0 / Real.sqrt (1 + Real.sin 0 ^ 2) = 1 := by simp
  rw [e] at h
  refine h.congr' ?_
  filter_upwards with x
  simp [slope, div_eq_inv_mul]
theorem tendsto_arcosh_two_sub_cos_div_abs :
    Tendsto (fun p : ℝ => Real.arcosh (2 - Real.cos p) / |p|) (𝓝[≠] 0) (𝓝 1) := by
  have hpi := Real.pi_pos
  have hhalf : Tendsto (fun p : ℝ => |p| / 2) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous fun p : ℝ => |p| / 2 := continuous_abs.div_const 2
      have h := hc.tendsto 0
      simp only [abs_zero, zero_div] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with p hp
      have hp0 : p ≠ 0 := hp
      simpa using hp0
  refine (tendsto_arsinh_sin_div_self.comp hhalf).congr' ?_
  have hnear : ∀ᶠ p in 𝓝[≠] (0 : ℝ), p ∈ Icc (-Real.pi) Real.pi :=
    nhdsWithin_le_nhds (Icc_mem_nhds (by linarith) hpi)
  filter_upwards [hnear, self_mem_nhdsWithin] with p hp hp0
  have hne : |p| ≠ 0 := abs_ne_zero.2 hp0
  simp only [Function.comp]
  rw [arcosh_two_sub_cos, abs_sin_half_eq hp]
  field_simp
theorem chordEndpoints_holds : ChordEndpoints := by
  have h3 : Real.arcosh 3 = 2 * Real.log (1 + Real.sqrt 2) := by
    have h := arcosh_two_sub_cos Real.pi
    rw [Real.cos_pi, Real.sin_pi_div_two, abs_one, arsinh_one_eq_log] at h
    rw [← h]
    norm_num
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hpos : 0 < 1 + Real.sqrt 2 := by linarith
  refine ⟨h3, ?_, ?_, ?_, ?_, tendsto_arcosh_two_sub_cos_div_abs⟩
  · rw [Real.cos_zero, show (2 : ℝ) - 1 = 1 by norm_num, Real.arcosh_zero]
  · rw [Real.cos_pi]
    norm_num
  · rw [h3]
    unfold chordSlopeConstant
    simp only [sub_zero]
    ring
  · rw [h3, neg_eq_neg_one_mul, ← mul_assoc, mul_comm, ← Real.rpow_def_of_pos hpos]
    have e : (1 + Real.sqrt 2) ^ ((-1 : ℝ) * 2) = ((1 + Real.sqrt 2) ^ 2)⁻¹ := by
      rw [show ((-1 : ℝ) * 2) = -((2 : ℕ) : ℝ) by norm_num, Real.rpow_neg hpos.le,
        Real.rpow_natCast]
    rw [e]
    field_simp
    nlinarith
theorem statement_holds : Statement :=
  ⟨boundOnInterval_holds, conditionsEquiv_holds, chordEndpoints_holds⟩
end YangMills.Construction.EnergyMomentum.ArcoshCurve
