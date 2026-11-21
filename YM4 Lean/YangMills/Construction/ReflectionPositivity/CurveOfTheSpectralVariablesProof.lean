import YangMills.Construction.EnergyMomentum.ArcoshCurveChordProof
import YangMills.Construction.Matrices.ExpLogEstimatesProof
import YangMills.Construction.ReflectionPositivity.BoundedMomentumDensityWithReflectionSizesProof
import YangMills.Construction.ReflectionPositivity.CurveOfTheSpectralVariables
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralCurve
theorem norm_one_sub_phaseOf_sq (u : ℝ) :
    ‖1 - phaseOf u‖ ^ 2 = 2 - 2 * Real.cos u := by apply _root_.YangMills.Construction.EnergyMomentum.ArcoshCurve.norm_one_sub_exp_I_mul_sq <;> assumption
theorem one_sub_expNegEnergy_sq (E : ℝ) :
    (1 - expNegEnergy E) ^ 2 = 2 * expNegEnergy E * (Real.cosh E - 1) := by
  have h : Real.exp E * Real.exp (-E) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [Real.cosh_eq, expNegEnergy]
  linear_combination -h
theorem cos_eq_one_sub_two_mul_sin_half_sq (u : ℝ) :
    Real.cos u = 1 - 2 * Real.sin (u / 2) ^ 2 := by apply _root_.YangMills.Construction.EnergyMomentum.ArcoshCurve.cos_eq_one_sub_two_sin_half_sq <;> assumption
theorem cosh_eq_one_add_two_mul_sinh_half_sq (E : ℝ) :
    Real.cosh E = 1 + 2 * Real.sinh (E / 2) ^ 2 := by
  have h := Real.cosh_two_mul (E / 2)
  have e : 2 * (E / 2) = E := by ring
  rw [e] at h
  nlinarith [Real.cosh_sq (E / 2)]
theorem defect_eq_cosh_add_cos (E u : ℝ) :
    (1 - expNegEnergy E) ^ 2 - expNegEnergy E * ‖1 - phaseOf u‖ ^ 2 =
      2 * expNegEnergy E * (Real.cosh E + Real.cos u - 2) := by
  rw [one_sub_expNegEnergy_sq, norm_one_sub_phaseOf_sq]
  ring
theorem cosh_add_cos_eq_sinh_sq_sub_sin_sq (E u : ℝ) :
    2 * expNegEnergy E * (Real.cosh E + Real.cos u - 2) =
      4 * expNegEnergy E * (Real.sinh (E / 2) ^ 2 - Real.sin (u / 2) ^ 2) := by
  rw [cosh_eq_one_add_two_mul_sinh_half_sq, cos_eq_one_sub_two_mul_sin_half_sq]
  ring
theorem aboveCurve_iff (E u : ℝ) :
    AboveCurve (expNegEnergy E) (phaseOf u) ↔
      Real.sin (u / 2) ^ 2 ≤ Real.sinh (E / 2) ^ 2 := by
  have hw : 0 < expNegEnergy E := Real.exp_pos _
  have h := (defect_eq_cosh_add_cos E u).trans (cosh_add_cos_eq_sinh_sq_sub_sin_sq E u)
  have h4 : 0 < 4 * expNegEnergy E := by positivity
  unfold AboveCurve
  constructor
  · intro hc
    have h0 : 0 ≤ 4 * expNegEnergy E * (Real.sinh (E / 2) ^ 2 - Real.sin (u / 2) ^ 2) := by
      rw [← h]
      linarith
    have h1 := (mul_nonneg_iff_of_pos_left h4).1 h0
    linarith
  · intro hc
    have h0 : 0 ≤ 4 * expNegEnergy E * (Real.sinh (E / 2) ^ 2 - Real.sin (u / 2) ^ 2) :=
      mul_nonneg h4.le (sub_nonneg.2 hc)
    rw [← h] at h0
    linarith
theorem abs_sin_half_le_sinh_half {E u : ℝ} (hE : 0 ≤ E)
    (h : AboveCurve (expNegEnergy E) (phaseOf u)) :
    |Real.sin (u / 2)| ≤ Real.sinh (E / 2) := by
  have h0 : 0 ≤ Real.sinh (E / 2) := Real.sinh_nonneg_iff.2 (by positivity)
  have h1 := sq_le_sq.1 ((aboveCurve_iff E u).1 h)
  rwa [abs_of_nonneg h0] at h1
theorem natCast_mul_sinh_le_sinh_mul {x : ℝ} (hx : 0 ≤ x) (k : ℕ) :
    (k : ℝ) * Real.sinh x ≤ Real.sinh ((k : ℝ) * x) := by
  induction k with
  | zero => simp
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) * x := by positivity
    have h1 : 0 ≤ Real.sinh ((n : ℝ) * x) := Real.sinh_nonneg_iff.2 hn
    have h2 : 0 ≤ Real.sinh x := Real.sinh_nonneg_iff.2 hx
    have c1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have c2 : 1 ≤ Real.cosh ((n : ℝ) * x) := Real.one_le_cosh _
    have e : ((n + 1 : ℕ) : ℝ) * x = (n : ℝ) * x + x := by
      push_cast
      ring
    rw [e, Real.sinh_add]
    push_cast
    nlinarith [mul_nonneg h1 (sub_nonneg.2 c1), mul_nonneg h2 (sub_nonneg.2 c2)]
theorem abs_sin_natCast_mul_le (y : ℝ) (k : ℕ) :
    |Real.sin ((k : ℝ) * y)| ≤ (k : ℝ) * |Real.sin y| := by
  induction k with
  | zero => simp
  | succ n ih =>
    have e : ((n + 1 : ℕ) : ℝ) * y = (n : ℝ) * y + y := by
      push_cast
      ring
    have c1 : |Real.cos y| ≤ 1 := abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    have c2 : |Real.cos ((n : ℝ) * y)| ≤ 1 :=
      abs_le.2 ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    rw [e, Real.sin_add]
    have h1 := abs_add_le (Real.sin ((n : ℝ) * y) * Real.cos y)
      (Real.cos ((n : ℝ) * y) * Real.sin y)
    rw [abs_mul, abs_mul] at h1
    have h2 := mul_le_mul_of_nonneg_left c1 (abs_nonneg (Real.sin ((n : ℝ) * y)))
    have h3 := mul_le_mul_of_nonneg_right c2 (abs_nonneg (Real.sin y))
    push_cast
    linarith
theorem expNegEnergy_pow (E : ℝ) (k : ℕ) : expNegEnergy E ^ k = expNegEnergy ((k : ℝ) * E) := by
  rw [expNegEnergy, expNegEnergy, ← Real.exp_nat_mul]
  congr 1
  ring
theorem phaseOf_pow (u : ℝ) (k : ℕ) : phaseOf u ^ k = phaseOf ((k : ℝ) * u) := by
  rw [phaseOf, phaseOf, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring
theorem powersStayAbove {E : ℝ} (u : ℝ) (k : ℕ) (hE : 0 ≤ E) : PowersStayAbove E u k := by
  intro h
  rw [expNegEnergy_pow, phaseOf_pow, aboveCurve_iff]
  have h1 := abs_sin_half_le_sinh_half hE h
  have h2 := natCast_mul_sinh_le_sinh_mul (x := E / 2) (by positivity) k
  have h3 := abs_sin_natCast_mul_le (u / 2) k
  have e1 : (k : ℝ) * u / 2 = (k : ℝ) * (u / 2) := by ring
  have e2 : (k : ℝ) * E / 2 = (k : ℝ) * (E / 2) := by ring
  rw [e1, e2]
  have h0 : 0 ≤ Real.sinh ((k : ℝ) * (E / 2)) := Real.sinh_nonneg_iff.2 (by positivity)
  rw [sq_le_sq, abs_of_nonneg h0]
  have h4 := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg (α := ℝ) k)
  linarith
theorem concaveOn_arsinh_sin :
    ConcaveOn ℝ (Set.Icc 0 (Real.pi / 2)) (fun x => Real.arsinh (Real.sin x)) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x => Real.arsinh (Real.sin x))
      ((√(1 + Real.sin x ^ 2))⁻¹ * Real.cos x) x := fun x =>
    (Real.hasDerivAt_arsinh _).comp x (Real.hasDerivAt_sin x)
  have hpi := Real.pi_pos
  apply AntitoneOn.concaveOn_of_deriv (convex_Icc _ _)
  · exact Real.continuous_sin.arsinh.continuousOn
  · exact fun x _ => (hderiv x).differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro a ha b hb hab
    rw [(hderiv a).deriv, (hderiv b).deriv]
    have hsin : Real.sin a ≤ Real.sin b :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [ha.1]) hb.2.le hab
    have ha0 : 0 ≤ Real.sin a :=
      Real.sin_nonneg_of_nonneg_of_le_pi ha.1.le (by linarith [ha.2])
    have hcos : Real.cos b ≤ Real.cos a :=
      Real.cos_le_cos_of_nonneg_of_le_pi ha.1.le (by linarith [hb.2]) hab
    have hcb : 0 ≤ Real.cos b :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hb.1]) hb.2.le
    have hsq : Real.sin a ^ 2 ≤ Real.sin b ^ 2 := pow_le_pow_left₀ ha0 hsin 2
    have hroot : √(1 + Real.sin a ^ 2) ≤ √(1 + Real.sin b ^ 2) :=
      Real.sqrt_le_sqrt (by linarith)
    have hpos : 0 < √(1 + Real.sin a ^ 2) := Real.sqrt_pos.2 (by positivity)
    have hinv : (√(1 + Real.sin b ^ 2))⁻¹ ≤ (√(1 + Real.sin a ^ 2))⁻¹ := inv_anti₀ hpos hroot
    exact mul_le_mul hinv hcos hcb (inv_nonneg.2 hpos.le)
theorem arsinh_one_eq_log : Real.arsinh 1 = Real.log (1 + √2) := by apply _root_.YangMills.Construction.EnergyMomentum.ArcoshCurve.arsinh_one_eq_log <;> assumption
theorem chord_le_arsinh_sin {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    2 * x / Real.pi * Real.log (1 + √2) ≤ Real.arsinh (Real.sin x) := by
  have hpi := Real.pi_pos
  have hs0 : 0 ≤ 2 * x / Real.pi := by positivity
  have hs1 : 2 * x / Real.pi ≤ 1 := by
    rw [div_le_one hpi]
    linarith
  have m0 : (0 : ℝ) ∈ Set.Icc 0 (Real.pi / 2) := Set.left_mem_Icc.2 (by positivity)
  have m1 : Real.pi / 2 ∈ Set.Icc 0 (Real.pi / 2) := Set.right_mem_Icc.2 (by positivity)
  have hs2 : 0 ≤ 1 - 2 * x / Real.pi := by linarith
  have hc := concaveOn_arsinh_sin.2 m0 m1 hs2 hs0 (by ring)
  have e : (1 - 2 * x / Real.pi) * 0 + 2 * x / Real.pi * (Real.pi / 2) = x := by
    field_simp
    ring
  simp only [smul_eq_mul, e, Real.sin_zero, Real.arsinh_zero, Real.sin_pi_div_two,
    arsinh_one_eq_log] at hc
  linarith
theorem abs_sin_half_eq_sin_abs_half {u : ℝ} (hu : |u| ≤ Real.pi) :
    |Real.sin (u / 2)| = Real.sin (|u| / 2) := by apply _root_.YangMills.Construction.Matrices.ComplexMatrix2.ExpLogEstimates.abs_sin_half_eq <;> assumption
theorem slopeConstant_pos : 0 < slopeConstant := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.MomentumDensityBound.slopeConstant_pos <;> assumption
theorem aboveCone {E : ℝ} (u : ℝ) (hE : 0 ≤ E) : AboveCone E u := by
  intro h hu
  have h1 := abs_sin_half_le_sinh_half hE h
  have hfirst : E ≥ 2 * Real.arsinh |Real.sin (u / 2)| := by
    have h2 := Real.arsinh_le_arsinh.2 h1
    rw [Real.arsinh_sinh] at h2
    linarith
  have hsecond : 2 * Real.arsinh |Real.sin (u / 2)| ≥ slopeConstant * |u| := by
    have h2 := chord_le_arsinh_sin (x := |u| / 2) (by positivity) (by linarith)
    rw [abs_sin_half_eq_sin_abs_half hu]
    have e : slopeConstant * |u| = 2 * (2 * (|u| / 2) / Real.pi * Real.log (1 + √2)) := by
      unfold slopeConstant
      ring
    rw [e]
    linarith
  refine ⟨hfirst, hsecond, fun hE0 => ?_⟩
  have hk := slopeConstant_pos
  have h3 : slopeConstant * |u| ≤ 0 := by linarith
  have h4 : |u| ≤ 0 := by
    by_contra hc
    exact absurd (mul_pos hk (not_le.1 hc)) (not_lt.2 h3)
  exact abs_eq_zero.1 (le_antisymm h4 (abs_nonneg u))
theorem curveFacts : CurveFacts := fun E u k hE _ =>
  ⟨⟨defect_eq_cosh_add_cos E u, cosh_add_cos_eq_sinh_sq_sub_sin_sq E u⟩, powersStayAbove u k hE,
    aboveCone u hE⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures.SpectralCurve
