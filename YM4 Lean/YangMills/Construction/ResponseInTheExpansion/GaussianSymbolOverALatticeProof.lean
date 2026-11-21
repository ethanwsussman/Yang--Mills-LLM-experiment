import YangMills.Construction.ResponseInTheExpansion.GaussianSymbolOverALattice
import YangMills.Construction.ResponseInTheExpansion.HeatSumOnALattice
import YangMills.Construction.ResponseInTheExpansion.ProductOfSumsOverALattice
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.LatticeFourier
namespace GaussianSymbol
private def primitiveCubic (c t : ℝ) : ℝ := (c⁻¹ * t⁻¹ + (c ^ 2)⁻¹) * Real.exp (-(c / t))
private def primitiveQuartic (c t : ℝ) : ℝ :=
  (c⁻¹ * t⁻¹ ^ 2 + 2 * (c ^ 2)⁻¹ * t⁻¹ + 2 * (c ^ 3)⁻¹) * Real.exp (-(c / t))
private lemma hasDerivAt_exp_neg_div (c t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t : ℝ => Real.exp (-(c / t))) (c * (t ^ 2)⁻¹ * Real.exp (-(c / t))) t := by
  have h1 : HasDerivAt (fun t : ℝ => -(c / t)) (c * (t ^ 2)⁻¹) t := by
    have h2 := (hasDerivAt_inv ht.ne').const_mul (-c)
    have e : (fun t : ℝ => -(c / t)) = fun y => -c * y⁻¹ := by
      funext y
      rw [div_eq_mul_inv]
      ring
    rw [e]
    refine h2.congr_deriv ?_
    ring
  have := h1.exp
  refine this.congr_deriv ?_
  ring
private lemma hasDerivAt_primitiveCubic (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (primitiveCubic c) ((t ^ 3)⁻¹ * Real.exp (-(c / t))) t := by
  have h0 := hasDerivAt_inv ht.ne'
  have h1 := ((h0.const_mul c⁻¹).add_const ((c ^ 2)⁻¹)).mul (hasDerivAt_exp_neg_div c t ht)
  refine h1.congr_deriv ?_
  field_simp
  ring
private lemma hasDerivAt_primitiveQuartic (c t : ℝ) (hc : 0 < c) (ht : 0 < t) :
    HasDerivAt (primitiveQuartic c) ((t ^ 4)⁻¹ * Real.exp (-(c / t))) t := by
  have h0 := hasDerivAt_inv ht.ne'
  have h1 := (((h0.pow 2).const_mul c⁻¹).add (h0.const_mul (2 * (c ^ 2)⁻¹))).add_const (2 * (c ^ 3)⁻¹)
  have h2 := h1.mul (hasDerivAt_exp_neg_div c t ht)
  refine h2.congr_deriv ?_
  simp only [Pi.add_apply, Pi.pow_apply]
  push_cast
  field_simp
  ring
private lemma abs_exp_neg_sub_taylor_le (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    |Real.exp (-x) - (1 - x + x ^ 2 / 2)| ≤ x ^ 3 := by
  have hx : |(-x)| ≤ 1 := by rwa [abs_neg, abs_of_nonneg h0]
  have := Real.exp_bound hx (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, abs_neg, abs_of_nonneg h0] at this
  norm_num [Nat.factorial] at this
  have e : Real.exp (-x) - (1 - x + x ^ 2 / 2) = Real.exp (-x) - (1 + -x + x ^ 2 / 2) := by ring
  rw [e]
  have h3 : 0 ≤ x ^ 3 := by positivity
  linarith
private lemma abs_primitiveCubic_sub_limit_le (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T) :
    |primitiveCubic c T - (c ^ 2)⁻¹| ≤ 3 * (T ^ 2)⁻¹ := by
  set x := c / T with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hT]; exact hcT
  have hb := abs_exp_neg_sub_taylor_le x hx0 hx1
  set ρ := Real.exp (-x) - (1 - x + x ^ 2 / 2) with hρ
  have hE : Real.exp (-x) = 1 - x + x ^ 2 / 2 + ρ := by rw [hρ]; ring
  have e1 : primitiveCubic c T - (c ^ 2)⁻¹ = (c ^ 2)⁻¹ * ((1 + x) * Real.exp (-x) - 1) := by
    unfold primitiveCubic
    rw [← hx, hx]
    field_simp <;> ring
  have e2 : (T ^ 2)⁻¹ = (c ^ 2)⁻¹ * x ^ 2 := by
    rw [hx]
    field_simp
  rw [e1, e2, hE, abs_mul, abs_of_pos (by positivity : 0 < (c ^ 2)⁻¹)]
  have hfin : |(1 + x) * (1 - x + x ^ 2 / 2 + ρ) - 1| ≤ 3 * x ^ 2 := by
    have hr := abs_le.1 hb
    have hx3 : x ^ 3 ≤ x ^ 2 := by nlinarith [sq_nonneg x]
    rw [abs_le]
    constructor <;> nlinarith [hr.1, hr.2, sq_nonneg x]
  have hc2 : 0 < (c ^ 2)⁻¹ := by positivity
  nlinarith
private lemma abs_primitiveQuartic_sub_limit_le (c T : ℝ) (hc : 0 < c) (hT : 0 < T) (hcT : c ≤ T) :
    |primitiveQuartic c T - 2 * (c ^ 3)⁻¹| ≤ 6 * (T ^ 3)⁻¹ := by
  set x := c / T with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by rw [hx, div_le_one hT]; exact hcT
  have hb := abs_exp_neg_sub_taylor_le x hx0 hx1
  set ρ := Real.exp (-x) - (1 - x + x ^ 2 / 2) with hρ
  have hE : Real.exp (-x) = 1 - x + x ^ 2 / 2 + ρ := by rw [hρ]; ring
  have e1 : primitiveQuartic c T - 2 * (c ^ 3)⁻¹ = (c ^ 3)⁻¹ * ((x ^ 2 + 2 * x + 2) * Real.exp (-x) - 2) := by
    unfold primitiveQuartic
    rw [← hx, hx]
    field_simp <;> ring
  have e2 : (T ^ 3)⁻¹ = (c ^ 3)⁻¹ * x ^ 3 := by
    rw [hx]
    field_simp
  rw [e1, e2, hE, abs_mul, abs_of_pos (by positivity : 0 < (c ^ 3)⁻¹)]
  have hfin : |(x ^ 2 + 2 * x + 2) * (1 - x + x ^ 2 / 2 + ρ) - 2| ≤ 6 * x ^ 3 := by
    have hr := abs_le.1 hb
    have e3 : (x ^ 2 + 2 * x + 2) * (1 - x + x ^ 2 / 2 + ρ) - 2 =
        x ^ 4 / 2 + (x ^ 2 + 2 * x + 2) * ρ := by ring
    rw [e3]
    have hx4 : x ^ 4 ≤ x ^ 3 := by nlinarith [pow_nonneg hx0 3]
    have hp : x ^ 2 + 2 * x + 2 ≤ 5 := by nlinarith
    have hp0 : 0 ≤ x ^ 2 + 2 * x + 2 := by positivity
    have hm : |(x ^ 2 + 2 * x + 2) * ρ| ≤ 5 * x ^ 3 := by
      rw [abs_mul, abs_of_nonneg hp0]
      exact mul_le_mul hp hb (abs_nonneg _) (by norm_num)
    have hm' := abs_le.1 hm
    have hx30 : 0 ≤ x ^ 3 := by positivity
    have hx40 : 0 ≤ x ^ 4 := by positivity
    rw [abs_le]
    constructor <;> linarith [hm'.1, hm'.2]
  have hc3 : 0 < (c ^ 3)⁻¹ := by positivity
  nlinarith
private lemma continuousOn_inv_cube_mul_exp (c T : ℝ) :
    ContinuousOn (fun t : ℝ => (t ^ 3)⁻¹ * Real.exp (-(c / t))) (Set.Icc 1 T) := by
  intro t ht
  have h0 : t ≠ 0 := by have := ht.1; positivity
  have h3 : t ^ 3 ≠ 0 := pow_ne_zero 3 h0
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)
private lemma continuousOn_inv_fourth_mul_exp (c T : ℝ) :
    ContinuousOn (fun t : ℝ => (t ^ 4)⁻¹ * Real.exp (-(c / t))) (Set.Icc 1 T) := by
  intro t ht
  have h0 : t ≠ 0 := by have := ht.1; positivity
  have h3 : t ^ 4 ≠ 0 := pow_ne_zero 4 h0
  apply ContinuousAt.continuousWithinAt
  fun_prop (disch := assumption)
private def hessianPrimitive (d w c t : ℝ) : ℝ :=
  (16 * Real.pi ^ 2)⁻¹ * (d / 2 * primitiveCubic c t - w / 4 * primitiveQuartic c t)
private lemma heatKernelHessian_eq (t : ℝ) (ht : 0 < t) (z : Fin 4 → ℝ) (a b : Fin 4) :
    heatKernelHessian t z a b = (16 * Real.pi ^ 2)⁻¹ *
      ((if a = b then (1 : ℝ) else 0) / 2 * ((t ^ 3)⁻¹ * Real.exp (-((∑ i, z i ^ 2) / 4 / t))) -
        z a * z b / 4 * ((t ^ 4)⁻¹ * Real.exp (-((∑ i, z i ^ 2) / 4 / t)))) := by
  unfold heatKernelHessian
  have e : (∑ i, z i ^ 2) / (4 * t) = (∑ i, z i ^ 2) / 4 / t := by
    field_simp
  rw [e]
  split_ifs <;> field_simp <;> ring
private lemma greenHessian_eq (z : Fin 4 → ℝ) (a b : Fin 4) (hR : 0 < ∑ i, z i ^ 2) :
    greenHessian z a b = (16 * Real.pi ^ 2)⁻¹ *
      ((if a = b then (1 : ℝ) else 0) / 2 * (((∑ i, z i ^ 2) / 4) ^ 2)⁻¹ -
        z a * z b / 4 * (2 * (((∑ i, z i ^ 2) / 4) ^ 3)⁻¹)) := by
  unfold greenHessian
  set R := ∑ i, z i ^ 2 with hRdef
  split_ifs <;> field_simp <;> ring
private lemma integral_heatKernelHessian_sub_greenHessian (z : Fin 4 → ℝ) (a b : Fin 4) (T : ℝ)
    (hR1 : 1 ≤ ∑ i, z i ^ 2) (hT1 : 1 ≤ T) (hcT : (∑ i, z i ^ 2) / 4 ≤ T)
    (hzz : |z a * z b| ≤ ∑ i, z i ^ 2) :
    IntervalIntegrable (fun t => heatKernelHessian t z a b) MeasureTheory.volume 1 T ∧
    |(∫ t in (1 : ℝ)..T, heatKernelHessian t z a b) - greenHessian z a b| ≤
      384 * ((∑ i, z i ^ 2) ^ (-(5 / 2 : ℝ)) + (T ^ 2)⁻¹) := by
  set R := ∑ i, z i ^ 2 with hRdef
  have hR0 : 0 < R := by linarith
  set c := R / 4 with hc
  have hc0 : 0 < c := by positivity
  have hT0 : 0 < T := by linarith
  set d : ℝ := if a = b then 1 else 0 with hd
  have hd0 : 0 ≤ d := by rw [hd]; split_ifs <;> norm_num
  have hd1 : d ≤ 1 := by rw [hd]; split_ifs <;> norm_num
  set w := z a * z b with hw
  have hcont : ContinuousOn (fun t => heatKernelHessian t z a b) (Set.Icc 1 T) := by
    have h1 : ContinuousOn (fun t : ℝ => (16 * Real.pi ^ 2)⁻¹ *
        (d / 2 * ((t ^ 3)⁻¹ * Real.exp (-(c / t))) - w / 4 * ((t ^ 4)⁻¹ * Real.exp (-(c / t)))))
        (Set.Icc 1 T) :=
      continuousOn_const.mul ((continuousOn_const.mul (continuousOn_inv_cube_mul_exp c T)).sub
        (continuousOn_const.mul (continuousOn_inv_fourth_mul_exp c T)))
    refine h1.congr fun t ht => ?_
    exact heatKernelHessian_eq t (by have := ht.1; linarith) z a b
  have hint : IntervalIntegrable (fun t => heatKernelHessian t z a b) MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hT1]
  refine ⟨hint, ?_⟩
  have hder : ∀ t ∈ Set.uIcc 1 T, HasDerivAt (hessianPrimitive d w c) (heatKernelHessian t z a b) t := by
    intro t ht
    rw [Set.uIcc_of_le hT1] at ht
    have ht0 : 0 < t := by have := ht.1; linarith
    rw [heatKernelHessian_eq t ht0 z a b]
    exact (((hasDerivAt_primitiveCubic c t hc0 ht0).const_mul (d / 2)).sub
      ((hasDerivAt_primitiveQuartic c t hc0 ht0).const_mul (w / 4))).const_mul _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint, greenHessian_eq z a b hR0]
  set k16 : ℝ := (16 * Real.pi ^ 2)⁻¹ with hk
  have hk0 : 0 < k16 := by positivity
  have hk1 : k16 ≤ 1 / 144 := by
    rw [hk, inv_eq_one_div]
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith [Real.pi_gt_three]
  have hwR : |w| ≤ 4 * c := by rw [hc]; linarith
  have hT3 := abs_primitiveCubic_sub_limit_le c T hc0 hT0 hcT
  have hT4 := abs_primitiveQuartic_sub_limit_le c T hc0 hT0 hcT
  have hA : |hessianPrimitive d w c T - k16 * (d / 2 * (c ^ 2)⁻¹ - w / 4 * (2 * (c ^ 3)⁻¹))| ≤
      (T ^ 2)⁻¹ := by
    have e1 : hessianPrimitive d w c T - k16 * (d / 2 * (c ^ 2)⁻¹ - w / 4 * (2 * (c ^ 3)⁻¹)) =
        k16 * (d / 2 * (primitiveCubic c T - (c ^ 2)⁻¹) -
          w / 4 * (primitiveQuartic c T - 2 * (c ^ 3)⁻¹)) := by
      unfold hessianPrimitive
      ring
    rw [e1, abs_mul, abs_of_pos hk0]
    have h1 : |d / 2 * (primitiveCubic c T - (c ^ 2)⁻¹)| ≤ 1 / 2 * (3 * (T ^ 2)⁻¹) := by
      rw [abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul (by linarith) hT3 (abs_nonneg _) (by norm_num)
    have h2 : |w / 4 * (primitiveQuartic c T - 2 * (c ^ 3)⁻¹)| ≤ c * (6 * (T ^ 3)⁻¹) := by
      rw [abs_mul, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      exact mul_le_mul (by linarith) hT4 (abs_nonneg _) hc0.le
    have h3 : c * (6 * (T ^ 3)⁻¹) ≤ 6 * (T ^ 2)⁻¹ := by
      have e2 : 6 * (T ^ 2)⁻¹ = T * (6 * (T ^ 3)⁻¹) := by
        field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_right hcT (by positivity)
    have hT2 : 0 ≤ (T ^ 2)⁻¹ := by positivity
    have h4 := abs_sub (d / 2 * (primitiveCubic c T - (c ^ 2)⁻¹))
      (w / 4 * (primitiveQuartic c T - 2 * (c ^ 3)⁻¹))
    have h5 : |d / 2 * (primitiveCubic c T - (c ^ 2)⁻¹) -
        w / 4 * (primitiveQuartic c T - 2 * (c ^ 3)⁻¹)| ≤ 8 * (T ^ 2)⁻¹ := by
      linarith
    calc k16 * _ ≤ 1 / 144 * (8 * (T ^ 2)⁻¹) := mul_le_mul hk1 h5 (abs_nonneg _) (by norm_num)
      _ ≤ (T ^ 2)⁻¹ := by linarith
  have hc4 : c⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ hc0 (by norm_num)]
    rw [hc]
    linarith
  have hE : Real.exp (-c) ≤ 384 * R ^ (-(5 / 2 : ℝ)) := by
    have h1 := Real.pow_div_factorial_le_exp c hc0.le 3
    have h2 : Real.exp (-c) ≤ 6 * (c ^ 3)⁻¹ := by
      rw [Real.exp_neg, ← one_div, ← one_div, mul_one_div, div_le_div_iff₀ (Real.exp_pos _) (by positivity)]
      have : (Nat.factorial 3 : ℝ) = 6 := by norm_num [Nat.factorial]
      rw [this, div_le_iff₀ (by norm_num)] at h1
      linarith
    have h3 : (R ^ 3)⁻¹ ≤ R ^ (-(5 / 2 : ℝ)) := by
      have h4 := Real.rpow_le_rpow_of_exponent_le hR1 (show (-(3 : ℝ)) ≤ -(5 / 2 : ℝ) by norm_num)
      rwa [Real.rpow_neg hR0.le, Real.rpow_ofNat] at h4
    have h5 : 6 * (c ^ 3)⁻¹ = 384 * (R ^ 3)⁻¹ := by
      rw [hc]
      field_simp
      norm_num
    rw [h5] at h2
    linarith
  have hB : |hessianPrimitive d w c 1| ≤ Real.exp (-c) := by
    have he0 : 0 < Real.exp (-c) := Real.exp_pos _
    have hY3 : primitiveCubic c 1 = (c⁻¹ + (c ^ 2)⁻¹) * Real.exp (-c) := by
      simp [primitiveCubic]
    have hY4 : primitiveQuartic c 1 = (c⁻¹ + 2 * (c ^ 2)⁻¹ + 2 * (c ^ 3)⁻¹) * Real.exp (-c) := by
      simp [primitiveQuartic]
    have hi2 : (c ^ 2)⁻¹ = c⁻¹ ^ 2 := by rw [inv_pow]
    have hi3 : (c ^ 3)⁻¹ = c⁻¹ ^ 3 := by rw [inv_pow]
    set v := c⁻¹ with hv
    have hv0 : 0 < v := by positivity
    have h1 : |d / 2 * primitiveCubic c 1| ≤ 10 * Real.exp (-c) := by
      rw [hY3, hi2, abs_mul, abs_of_nonneg (by positivity), abs_mul, abs_of_pos he0,
        abs_of_pos (by positivity)]
      rw [← mul_assoc]
      refine mul_le_mul_of_nonneg_right ?_ he0.le
      nlinarith
    have h2 : |w / 4 * primitiveQuartic c 1| ≤ 41 * Real.exp (-c) := by
      have hP0 : 0 ≤ v + 2 * v ^ 2 + 2 * v ^ 3 := by positivity
      rw [hY4, hi2, hi3, ← mul_assoc, abs_mul, abs_of_pos he0, abs_mul, abs_of_nonneg hP0, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      refine mul_le_mul_of_nonneg_right ?_ he0.le
      have hcv : c * v = 1 := by rw [hv]; field_simp
      have e1 : c * (v + 2 * v ^ 2 + 2 * v ^ 3) = 1 + 2 * v + 2 * v ^ 2 := by
        calc c * (v + 2 * v ^ 2 + 2 * v ^ 3) = (c * v) * (1 + 2 * v + 2 * v ^ 2) := by ring
          _ = _ := by rw [hcv, one_mul]
      calc |w| / 4 * (v + 2 * v ^ 2 + 2 * v ^ 3) ≤ c * (v + 2 * v ^ 2 + 2 * v ^ 3) :=
            mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ ≤ 41 := by rw [e1]; nlinarith
    unfold hessianPrimitive
    rw [abs_mul, abs_of_pos hk0]
    have h4 := abs_sub (d / 2 * primitiveCubic c 1) (w / 4 * primitiveQuartic c 1)
    have h5 : |d / 2 * primitiveCubic c 1 - w / 4 * primitiveQuartic c 1| ≤ 51 * Real.exp (-c) := by
      linarith
    calc k16 * _ ≤ 1 / 144 * (51 * Real.exp (-c)) := mul_le_mul hk1 h5 (abs_nonneg _) (by norm_num)
      _ ≤ Real.exp (-c) := by linarith
  have hfin : hessianPrimitive d w c T - hessianPrimitive d w c 1 -
      k16 * (d / 2 * (c ^ 2)⁻¹ - w / 4 * (2 * (c ^ 3)⁻¹)) =
      (hessianPrimitive d w c T - k16 * (d / 2 * (c ^ 2)⁻¹ - w / 4 * (2 * (c ^ 3)⁻¹))) -
        hessianPrimitive d w c 1 := by ring
  rw [hfin]
  have h6 := abs_sub (hessianPrimitive d w c T - k16 * (d / 2 * (c ^ 2)⁻¹ - w / 4 * (2 * (c ^ 3)⁻¹)))
    (hessianPrimitive d w c 1)
  have hT2 : 0 ≤ (T ^ 2)⁻¹ := by positivity
  linarith
private lemma integral_inv_cube_mul_exp_le (c T : ℝ) (hc : 0 < c) (hT : 1 ≤ T) :
    IntervalIntegrable (fun t : ℝ => (t ^ 3)⁻¹ * Real.exp (-(c / t))) MeasureTheory.volume 1 T ∧
    ∫ t in (1 : ℝ)..T, (t ^ 3)⁻¹ * Real.exp (-(c / t)) ≤ c⁻¹ * T⁻¹ + (c ^ 2)⁻¹ := by
  have hint : IntervalIntegrable (fun t : ℝ => (t ^ 3)⁻¹ * Real.exp (-(c / t)))
      MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [Set.uIcc_of_le hT]
    exact continuousOn_inv_cube_mul_exp c T
  refine ⟨hint, ?_⟩
  have hder : ∀ t ∈ Set.uIcc 1 T,
      HasDerivAt (primitiveCubic c) ((t ^ 3)⁻¹ * Real.exp (-(c / t))) t := by
    intro t ht
    rw [Set.uIcc_of_le hT] at ht
    exact hasDerivAt_primitiveCubic c t hc (by have := ht.1; linarith)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint]
  have h1 : 0 ≤ primitiveCubic c 1 := by
    unfold primitiveCubic
    positivity
  have h2 : primitiveCubic c T ≤ c⁻¹ * T⁻¹ + (c ^ 2)⁻¹ := by
    unfold primitiveCubic
    have hE : Real.exp (-(c / T)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ c / T := by positivity
      linarith
    have hp : 0 ≤ c⁻¹ * T⁻¹ + (c ^ 2)⁻¹ := by positivity
    nlinarith
  linarith
private lemma integral_mul_exp_neg_mul (w s T : ℝ) (hs : 0 < s) (hT : 1 ≤ T) :
    ∫ t in (1 : ℝ)..T, w * Real.exp (-(t * s)) = w * (Real.exp (-s) - Real.exp (-(T * s))) / s := by
  have hd : ∀ t ∈ Set.uIcc 1 T, HasDerivAt (fun t : ℝ => -w * Real.exp (-(t * s)) / s)
      (w * Real.exp (-(t * s))) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => -(t * s)) (-s) t := by
      have h0 := ((hasDerivAt_id t).mul_const s).neg
      exact h0.congr_deriv (by simp)
    have h3 := (h1.exp.const_mul (-w)).div_const s
    refine h3.congr_deriv ?_
    field_simp
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp only [one_mul]
  field_simp
  ring
private lemma gaussianSymbolTerm_eq_integral_add (N : ℕ) (z : Fin 4 → ℝ) (a b : Fin 4) (k : Fin 4 → ℤ)
    (T : ℝ) (hT : 1 ≤ T) :
    gaussianSymbolTerm N z a b k = (∫ t in (1 : ℝ)..T, heatLatticeTerm N t z a b k) +
      ((Real.exp (-(T * ∑ i, circleMomentum N (k i) ^ 2)) *
        (circleMomentum N (k a) * circleMomentum N (k b)) / ∑ i, circleMomentum N (k i) ^ 2 : ℝ) : ℂ) *
        Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ)) := by
  unfold gaussianSymbolTerm heatLatticeTerm
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_ofReal, ← add_mul]
  congr 1
  set s := ∑ i, circleMomentum N (k i) ^ 2 with hs
  set w := circleMomentum N (k a) * circleMomentum N (k b) with hw
  have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
  rcases hs0.eq_or_lt with h | h
  · have ha : circleMomentum N (k a) = 0 := by
      have h1 : circleMomentum N (k a) ^ 2 ≤ s := Finset.single_le_sum
        (f := fun i => circleMomentum N (k i) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      rw [← h] at h1
      nlinarith [sq_nonneg (circleMomentum N (k a))]
    have hw0 : w = 0 := by rw [hw, ha, zero_mul]
    simp [hw0]
  · rw [integral_mul_exp_neg_mul w s T h hT]
    push_cast
    have hc : (s : ℂ) ≠ 0 := by exact_mod_cast h.ne'
    field_simp
    ring
private lemma norm_heatLatticeTerm_le_one (N : ℕ) (z : Fin 4 → ℝ) (a b : Fin 4) (k : Fin 4 → ℤ)
    (t : ℝ) (ht : 1 ≤ t) :
    ‖heatLatticeTerm N t z a b k‖ ≤ ‖heatLatticeTerm N 1 z a b k‖ := by
  unfold heatLatticeTerm
  rw [norm_mul, norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, mul_one,
    Complex.norm_real, Complex.norm_real]
  set w := circleMomentum N (k a) * circleMomentum N (k b) with hw
  rw [norm_mul w, norm_mul w]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg w)
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.norm_of_nonneg (Real.exp_pos _).le]
  refine Real.exp_le_exp.2 ?_
  have hs0 : 0 ≤ ∑ i, circleMomentum N (k i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  nlinarith
end GaussianSymbol
open GaussianSymbol in
theorem gaussianSymbolLatticeStatement_of_heatLattice (hP : tsum_pi_prod_statement)
    (hH : poissonSummationHeatLatticeStatement) : gaussianSymbolLatticeStatement := by
  obtain ⟨C₁, hC₁⟩ := hH
  set e0 : ℤ → ℝ := fun n => Real.exp (-(4 * Real.pi ^ 2 * (n : ℝ) ^ 2)) with he0
  have he0s : Summable e0 := by
    refine (summable_pow_mul_jacobiTheta₂_term_bound 0 (T := 4 * Real.pi) (by positivity) 0).congr
      fun n => ?_
    simp only [pow_zero, one_mul, he0]
    congr 1
    ring
  set S : ℝ := ∑' n, e0 n with hS
  have hprod : HasSum (fun k : Fin 4 → ℤ => ∏ i, e0 (k i)) (S ^ 4) := by
    have hn : Summable fun m => ‖e0 m‖ := by
      refine he0s.congr fun m => ?_
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    have := (hP ℝ 4 (fun _ => e0) (fun _ => hn)).2
    simpa using this
  refine ⟨132 * |C₁| + 384 + S ^ 4, fun N z a b hN hz1 hzN => ?_⟩
  have hN' : (8 : ℝ) ≤ N := by exact_mod_cast hN
  set T : ℝ := (N : ℝ) ^ 2 with hT
  have hT1 : 1 ≤ T := by rw [hT]; nlinarith
  set R := ∑ i, z i ^ 2 with hR
  have hcT : R / 4 ≤ T := by
    have : ((N : ℝ) / 8) ^ 2 = T / 64 := by rw [hT]; ring
    rw [this] at hzN
    linarith
  have hzz : |z a * z b| ≤ R := by
    have ha : z a ^ 2 ≤ R := Finset.single_le_sum (f := fun i => z i ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ a)
    have hb : z b ^ 2 ≤ R := Finset.single_le_sum (f := fun i => z i ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)
    rw [abs_mul]
    nlinarith [sq_nonneg (|z a| - |z b|), sq_abs (z a), sq_abs (z b)]
  have hl : ∀ t, 1 ≤ t → t ≤ T → _ := fun t h1 h2 => hC₁ N t z a b hN h1 h2 hzN
  set A2 : (Fin 4 → ℤ) → ℂ := fun k =>
    ((Real.exp (-(T * ∑ i, circleMomentum N (k i) ^ 2)) *
      (circleMomentum N (k a) * circleMomentum N (k b)) / ∑ i, circleMomentum N (k i) ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * ((∑ i, circleMomentum N (k i) * z i : ℝ) : ℂ)) with hA2
  have hA2b : ∀ k, ‖A2 k‖ ≤ ∏ i, e0 (k i) := by
    intro k
    simp only [hA2]
    rw [norm_mul, mul_comm Complex.I, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real]
    set s := ∑ i, circleMomentum N (k i) ^ 2 with hs
    have hs0 : 0 ≤ s := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hEq : ∏ i, e0 (k i) = Real.exp (-(T * s)) := by
      simp only [he0]
      rw [← Real.exp_sum, Finset.sum_neg_distrib]
      congr 2
      rw [hs, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold circleMomentum
      rw [hT]
      field_simp
      ring
    rw [hEq, Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg hs0]
    have hE : 0 < Real.exp (-(T * s)) := Real.exp_pos _
    rcases hs0.eq_or_lt with h | h
    · rw [← h]
      simp
    · rw [div_le_iff₀ h]
      have ha : circleMomentum N (k a) ^ 2 ≤ s := Finset.single_le_sum
        (f := fun i => circleMomentum N (k i) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ a)
      have hb : circleMomentum N (k b) ^ 2 ≤ s := Finset.single_le_sum
        (f := fun i => circleMomentum N (k i) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)
      have hw : |circleMomentum N (k a) * circleMomentum N (k b)| ≤ s := by
        rw [abs_mul]
        nlinarith [sq_nonneg (|circleMomentum N (k a)| - |circleMomentum N (k b)|),
          sq_abs (circleMomentum N (k a)), sq_abs (circleMomentum N (k b))]
      exact mul_le_mul_of_nonneg_left hw hE.le
  have hA2s : Summable A2 := Summable.of_norm_bounded hprod.summable hA2b
  have hA2n : ‖∑' k, A2 k‖ ≤ S ^ 4 := tsum_of_norm_bounded hprod hA2b
  set f : ℝ → ℂ := fun t => ∑' k, heatLatticeTerm N t z a b k with hf
  have hsum1 : Summable fun k => ‖heatLatticeTerm N 1 z a b k‖ := (hl 1 le_rfl hT1).1.norm
  have hcont : ∀ k, Continuous fun t => heatLatticeTerm N t z a b k := by
    intro k
    unfold heatLatticeTerm
    fun_prop
  have hHS : HasSum (fun k => ∫ t in (1 : ℝ)..T, heatLatticeTerm N t z a b k)
      (∫ t in (1 : ℝ)..T, f t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun k _ => ‖heatLatticeTerm N 1 z a b k‖) (fun k => (hcont k).aestronglyMeasurable) ?_ ?_ ?_ ?_
    · refine fun k => Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le hT1] at ht
      exact norm_heatLatticeTerm_le_one N z a b k t ht.1.le
    · exact Filter.Eventually.of_forall fun t _ => hsum1
    · exact intervalIntegrable_const
    · refine Filter.Eventually.of_forall fun t ht => ?_
      rw [Set.uIoc_of_le hT1] at ht
      exact (hl t ht.1.le ht.2).1.hasSum
  have hgt : ∀ k, gaussianSymbolTerm N z a b k =
      (∫ t in (1 : ℝ)..T, heatLatticeTerm N t z a b k) + A2 k :=
    fun k => gaussianSymbolTerm_eq_integral_add N z a b k T hT1
  have hfun : gaussianSymbolTerm N z a b =
      fun k => (∫ t in (1 : ℝ)..T, heatLatticeTerm N t z a b k) + A2 k :=
    funext hgt
  have hTot := hHS.add hA2s.hasSum
  refine ⟨by rw [hfun]; exact hTot.summable, ?_⟩
  rw [hfun, hTot.tsum_eq]
  have hfc : ContinuousOn f (Set.Icc 1 T) := by
    refine continuousOn_tsum (fun k => (hcont k).continuousOn) hsum1 ?_
    intro k t ht
    exact norm_heatLatticeTerm_le_one N z a b k t ht.1
  have hfi : IntervalIntegrable f MeasureTheory.volume 1 T := by
    refine ContinuousOn.intervalIntegrable ?_
    rwa [Set.uIcc_of_le hT1]
  obtain ⟨hMi, hMb⟩ := integral_heatKernelHessian_sub_greenHessian z a b T hz1 hT1 hcT hzz
  set c' : ℝ := (N : ℝ) ^ 2 / 11 with hc'
  have hc'0 : 0 < c' := by positivity
  obtain ⟨hEi, hEb⟩ := integral_inv_cube_mul_exp_le c' T hc'0 hT1
  set Ninv : ℂ := ((N : ℂ) ^ 4)⁻¹ with hNinv
  have hNn : ‖Ninv‖ = ((N : ℝ) ^ 4)⁻¹ := by
    rw [hNinv, norm_inv, norm_pow, Complex.norm_natCast]
  have hdiff : ‖Ninv * (∫ t in (1 : ℝ)..T, f t) -
      ((∫ t in (1 : ℝ)..T, heatKernelHessian t z a b : ℝ) : ℂ)‖ ≤
      |C₁| * ∫ t in (1 : ℝ)..T, (t ^ 3)⁻¹ * Real.exp (-(c' / t)) := by
    have hMc : IntervalIntegrable (fun t => ((heatKernelHessian t z a b : ℝ) : ℂ))
        MeasureTheory.volume 1 T :=
      ⟨hMi.1.ofReal, hMi.2.ofReal⟩
    have e1 : Ninv * (∫ t in (1 : ℝ)..T, f t) -
        ((∫ t in (1 : ℝ)..T, heatKernelHessian t z a b : ℝ) : ℂ) =
        ∫ t in (1 : ℝ)..T, (Ninv * f t - ((heatKernelHessian t z a b : ℝ) : ℂ)) := by
      rw [intervalIntegral.integral_sub (hfi.const_mul _) hMc, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_ofReal]
    rw [e1, ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.norm_integral_le_of_norm_le hT1 ?_ (hEi.const_mul _)
    refine Filter.Eventually.of_forall fun t ht => ?_
    have hb := (hl t ht.1.le ht.2).2
    have ht0 : 0 < t := by linarith [ht.1]
    have e2 : (N : ℝ) ^ 2 / (11 * t) = c' / t := by
      rw [hc']
      field_simp
    rw [e2] at hb
    refine hb.trans ?_
    have hnn : 0 ≤ (t ^ 3)⁻¹ * Real.exp (-(c' / t)) := by positivity
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hnn
  have hE2 : c'⁻¹ * T⁻¹ + (c' ^ 2)⁻¹ = 132 * ((N : ℝ) ^ 4)⁻¹ := by
    rw [hc', hT]
    field_simp
    norm_num
  have hNpow : (N : ℝ) ^ (-(4 : ℤ)) = ((N : ℝ) ^ 4)⁻¹ := by
    rw [zpow_neg]
    norm_cast
  have hT2 : (T ^ 2)⁻¹ = ((N : ℝ) ^ 4)⁻¹ := by
    rw [hT]
    congr 1
    ring
  rw [hNpow]
  rw [hT2] at hMb
  set I1 : ℝ := ∫ t in (1 : ℝ)..T, heatKernelHessian t z a b with hI1
  set Nq : ℝ := ((N : ℝ) ^ 4)⁻¹ with hNq
  have hNq0 : 0 ≤ Nq := by positivity
  set Rq : ℝ := R ^ (-(5 / 2 : ℝ)) with hRq
  have hRq0 : 0 ≤ Rq := Real.rpow_nonneg (by linarith) _
  have hsplit : Ninv * ((∫ t in (1 : ℝ)..T, f t) + ∑' k, A2 k) - (greenHessian z a b : ℂ) =
      (Ninv * (∫ t in (1 : ℝ)..T, f t) - (I1 : ℂ)) + (((I1 - greenHessian z a b : ℝ)) : ℂ) +
        Ninv * ∑' k, A2 k := by
    push_cast
    ring
  rw [hsplit]
  have b1 : ‖Ninv * (∫ t in (1 : ℝ)..T, f t) - (I1 : ℂ)‖ ≤ |C₁| * (132 * Nq) := by
    refine hdiff.trans ?_
    rw [← hE2]
    exact mul_le_mul_of_nonneg_left hEb (abs_nonneg _)
  have b2 : ‖(((I1 - greenHessian z a b : ℝ)) : ℂ)‖ ≤ 384 * (Rq + Nq) := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hMb
  have b3 : ‖Ninv * ∑' k, A2 k‖ ≤ Nq * S ^ 4 := by
    rw [norm_mul, hNn]
    exact mul_le_mul_of_nonneg_left hA2n hNq0
  have n1 := norm_add_le ((Ninv * (∫ t in (1 : ℝ)..T, f t) - (I1 : ℂ)) +
    (((I1 - greenHessian z a b : ℝ)) : ℂ)) (Ninv * ∑' k, A2 k)
  have n2 := norm_add_le (Ninv * (∫ t in (1 : ℝ)..T, f t) - (I1 : ℂ))
    (((I1 - greenHessian z a b : ℝ)) : ℂ)
  have hC0 : 0 ≤ |C₁| := abs_nonneg _
  have hS4 : 0 ≤ S ^ 4 := by positivity
  calc _ ≤ |C₁| * (132 * Nq) + 384 * (Rq + Nq) + Nq * S ^ 4 := by linarith
    _ ≤ (132 * |C₁| + 384 + S ^ 4) * (Rq + Nq) := by
      nlinarith [mul_nonneg hC0 hRq0, mul_nonneg hS4 hRq0]
end YangMills.Construction.LatticeFourier
