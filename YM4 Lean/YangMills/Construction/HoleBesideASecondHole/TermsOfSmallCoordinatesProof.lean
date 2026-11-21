import YangMills.Construction.ColdChainAtEveryLevel.LastMisfitNearACell
import YangMills.Construction.ColdChainAtEveryLevel.RatesOfTheTerms
import YangMills.Construction.HoleBesideASecondHole.EachHoleIsFilledProof
import YangMills.Construction.HoleBesideASecondHole.NormsNearACell
import YangMills.Construction.HoleBesideASecondHole.TermsOfSmallCoordinates
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction
open BlockAverages CellTerms LumpContours
namespace SmallCellTerms
variable {F : BlockFrame}
theorem coe_mul_unitQuaternion (a b : UnitQuaternion) :
    ((a * b : UnitQuaternion) : ℍ[ℝ]) = (a : ℍ[ℝ]) * (b : ℍ[ℝ]) := rfl
theorem norm_exp_sub_one_sub_le {w : ℍ[ℝ]} (hw : w.re = 0) :
    ‖NormedSpace.exp w - 1 - w‖ ≤ 3 * ‖w‖ ^ 2 := by
  set θ := ‖w‖ with hθ
  have hθ0 : 0 ≤ θ := norm_nonneg _
  by_cases h1 : θ ≤ 1
  · have hs : (Real.sin θ / θ) = Real.sinc θ ∨ θ = 0 := by
      by_cases h0 : θ = 0
      · exact Or.inr h0
      · exact Or.inl (Real.sinc_of_ne_zero h0).symm
    rcases hs with hs | h0
    · have e : NormedSpace.exp w - 1 - w = (((Real.cos θ - 1 : ℝ)) : ℍ[ℝ]) + (Real.sinc θ - 1) • w := by
        rw [exp_eq_of_re_eq_zero hw, ← hθ, hs, sub_smul, one_smul]
        push_cast
        abel
      rw [e]
      refine (norm_add_le _ _).trans ?_
      rw [Quaternion.norm_coe, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, ← hθ]
      have hc := Real.one_sub_sq_div_two_le_cos (x := θ)
      have hc1 := Real.cos_le_one θ
      have h2 : |Real.cos θ - 1| ≤ θ ^ 2 / 2 := by
        rw [abs_le]
        constructor <;> linarith [sq_nonneg θ]
      have h3 := abs_sinc_sub_one_le hθ0 h1
      have h4 : |Real.sinc θ - 1| * θ ≤ θ ^ 2 / 4 * 1 :=
        mul_le_mul h3 h1 hθ0 (by positivity)
      nlinarith [sq_nonneg θ]
    · have hw0 : w = 0 := norm_eq_zero.1 h0
      subst hw0
      simp
      exact sq_nonneg θ
  · push Not at h1
    have e1 : ‖NormedSpace.exp w‖ = 1 := by
      rw [Quaternion.norm_exp, hw]
      simp
    calc ‖NormedSpace.exp w - 1 - w‖ ≤ ‖NormedSpace.exp w‖ + ‖(1 : ℍ[ℝ])‖ + ‖w‖ :=
          (norm_sub_le _ _).trans (add_le_add_left (norm_sub_le _ _) _)
      _ = 2 + θ := by rw [e1, norm_one]; ring
      _ ≤ 3 * θ ^ 2 := by nlinarith
def linearDeviation (g : UnitQuaternion) (w : ℍ[ℝ]) : ℝ := ‖(g : ℍ[ℝ]) - 1 - w‖
theorem linearDeviation_conj (t g : UnitQuaternion) (w : ℍ[ℝ]) :
    linearDeviation (t * g * t⁻¹) (adjointAction t w) = linearDeviation g w := by
  unfold linearDeviation adjointAction
  have e : ((t * g * t⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 - (t : ℍ[ℝ]) * w * ((t⁻¹ : UnitQuaternion) : ℍ[ℝ]) =
      (t : ℍ[ℝ]) * ((g : ℍ[ℝ]) - 1 - w) * ((t⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
    have h1 : (t : ℍ[ℝ]) * ((t⁻¹ : UnitQuaternion) : ℍ[ℝ]) = 1 := by
      rw [← Submonoid.coe_mul, mul_inv_cancel]
      rfl
    simp only [Submonoid.coe_mul, mul_sub, sub_mul, mul_one, h1]
  rw [e, norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion]
  ring
theorem linearDeviation_expUnit (w : imaginaryQuaternions) :
    linearDeviation (expUnit w) (w : ℍ[ℝ]) ≤ 3 * ‖(w : ℍ[ℝ])‖ ^ 2 := norm_exp_sub_one_sub_le w.2
theorem linearDeviation_expUnit_inv (w : imaginaryQuaternions) :
    linearDeviation (expUnit w)⁻¹ (-(w : ℍ[ℝ])) ≤ 3 * ‖(w : ℍ[ℝ])‖ ^ 2 := by
  have h := norm_exp_sub_one_sub_le w.2
  unfold linearDeviation
  have e : (((expUnit w)⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1 - -(w : ℍ[ℝ]) =
      star ((expUnit w : ℍ[ℝ]) - 1 - (w : ℍ[ℝ])) := by
    have hs : star (w : ℍ[ℝ]) = -(w : ℍ[ℝ]) := Quaternion.star_eq_neg.2 w.2
    rw [star_sub, star_sub, star_one, hs, coe_unitQuaternion_inv]
  rw [e, norm_star]
  exact h
theorem linearDeviation_mul_four_le (e1 e2 e3 e4 : UnitQuaternion) (w1 w2 w3 w4 : ℍ[ℝ]) :
    linearDeviation (e1 * e2 * e3 * e4) (w1 + w2 + w3 + w4) ≤
      linearDeviation e1 w1 + linearDeviation e2 w2 + linearDeviation e3 w3 + linearDeviation e4 w4 +
      (‖(e1 : ℍ[ℝ]) - 1‖ + ‖(e2 : ℍ[ℝ]) - 1‖ + ‖(e3 : ℍ[ℝ]) - 1‖ + ‖(e4 : ℍ[ℝ]) - 1‖) ^ 2 := by
  set a1 := (e1 : ℍ[ℝ]) - 1 with h1
  set a2 := (e2 : ℍ[ℝ]) - 1 with h2
  set a3 := (e3 : ℍ[ℝ]) - 1 with h3
  set a4 := (e4 : ℍ[ℝ]) - 1 with h4
  have c1 : (e1 : ℍ[ℝ]) = 1 + a1 := by rw [h1]; abel
  have c2 : (e2 : ℍ[ℝ]) = 1 + a2 := by rw [h2]; abel
  have c3 : (e3 : ℍ[ℝ]) = 1 + a3 := by rw [h3]; abel
  have c4 : (e4 : ℍ[ℝ]) = 1 + a4 := by rw [h4]; abel
  have hx : ‖(e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) - 1‖ ≤ ‖a1‖ + ‖a2‖ := norm_coe_mul_sub_one_le e1 e2
  have hy : ‖(e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) * (e3 : ℍ[ℝ]) - 1‖ ≤ ‖a1‖ + ‖a2‖ + ‖a3‖ :=
    (norm_coe_mul_sub_one_le (e1 * e2) e3).trans (add_le_add_left hx _)
  have e : (((e1 * e2 * e3 * e4 : UnitQuaternion)) : ℍ[ℝ]) - 1 - (w1 + w2 + w3 + w4) =
      (a1 - w1) + (a2 - w2) + (a3 - w3) + (a4 - w4) + a1 * a2 +
        ((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) - 1) * a3 + ((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) * (e3 : ℍ[ℝ]) - 1) * a4 := by
    simp only [Submonoid.coe_mul]
    rw [c1, c2, c3, c4]
    noncomm_ring
  unfold linearDeviation
  rw [e]
  have n1 : ‖a1 * a2‖ ≤ ‖a1‖ * ‖a2‖ := norm_mul_le _ _
  have n2 : ‖((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) - 1) * a3‖ ≤ (‖a1‖ + ‖a2‖) * ‖a3‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hx (norm_nonneg _))
  have n3 : ‖((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) * (e3 : ℍ[ℝ]) - 1) * a4‖ ≤ (‖a1‖ + ‖a2‖ + ‖a3‖) * ‖a4‖ :=
    (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right hy (norm_nonneg _))
  have t : ‖(a1 - w1) + (a2 - w2) + (a3 - w3) + (a4 - w4) + a1 * a2 +
        ((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) - 1) * a3 + ((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) * (e3 : ℍ[ℝ]) - 1) * a4‖ ≤
      ‖a1 - w1‖ + ‖a2 - w2‖ + ‖a3 - w3‖ + ‖a4 - w4‖ + ‖a1 * a2‖ +
        ‖((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) - 1) * a3‖ + ‖((e1 : ℍ[ℝ]) * (e2 : ℍ[ℝ]) * (e3 : ℍ[ℝ]) - 1) * a4‖ := by
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    refine (norm_add_le _ _).trans (add_le_add_left ?_ _)
    exact norm_add_le _ _
  nlinarith [norm_nonneg a1, norm_nonneg a2, norm_nonneg a3, norm_nonneg a4, mul_nonneg (norm_nonneg a1) (norm_nonneg a2),
    mul_nonneg (norm_nonneg a1) (norm_nonneg a3), mul_nonneg (norm_nonneg a1) (norm_nonneg a4),
    mul_nonneg (norm_nonneg a2) (norm_nonneg a3), mul_nonneg (norm_nonneg a2) (norm_nonneg a4),
    mul_nonneg (norm_nonneg a3) (norm_nonneg a4), sq_nonneg ‖a1‖, sq_nonneg ‖a2‖, sq_nonneg ‖a3‖, sq_nonneg ‖a4‖]
theorem plaquetteHolonomy_eq {j : ℕ} (X : F.GaugeField j) (p : F.Site j × Fin 4 × Fin 4) :
    plaquetteHolonomy X p = X p.1 p.2.1 * X (p.1 + unitStep j p.2.1) p.2.2 *
      (X (p.1 + unitStep j p.2.2) p.2.1)⁻¹ * (X p.1 p.2.2)⁻¹ := by
  have e1 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 - unitStep j p.2.1 = p.1 + unitStep j p.2.2 := by abel
  have e2 : p.1 + unitStep j p.2.1 + unitStep j p.2.2 + -unitStep j p.2.1 - unitStep j p.2.2 = p.1 := by abel
  simp only [plaquetteHolonomy, pathHolonomy, linkValue, stepDisplacement, if_true, Bool.false_eq_true, if_false,
    e1, e2, mul_one, mul_assoc]
theorem norm_coe_expUnit_sub_one_le (w : imaginaryQuaternions) :
    ‖(expUnit w : ℍ[ℝ]) - 1‖ ≤ ‖(w : ℍ[ℝ])‖ := norm_exp_sub_one_le w.2
theorem norm_plaquetteHolonomy_chart_sub_one_le (R : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    ‖((plaquetteHolonomy (fun x i => expUnit (u x i) * R x i) p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
      ‖linearizedCurl R u p‖ + plaquetteDefect R p +
        4 * (‖(u p.1 p.2.1 : ℍ[ℝ])‖ + ‖(u (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ +
          ‖(u (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ + ‖(u p.1 p.2.2 : ℍ[ℝ])‖) ^ 2 := by
  obtain ⟨x, μ, ν⟩ := p
  set r1 := R x μ with hr1
  set r2 := R (x + unitStep 0 μ) ν with hr2
  set r3 := R (x + unitStep 0 ν) μ with hr3
  set r4 := R x ν with hr4
  set u1 := u x μ with hu1
  set u2 := u (x + unitStep 0 μ) ν with hu2
  set u3 := u (x + unitStep 0 ν) μ with hu3
  set u4 := u x ν with hu4
  set t := r1 * r2 * r3⁻¹ with ht
  set t' := t * r4⁻¹ with ht'
  have hR : plaquetteHolonomy R (x, μ, ν) = t' := by
    rw [plaquetteHolonomy_eq]
  have hg : plaquetteHolonomy (fun x i => expUnit (u x i) * R x i) (x, μ, ν) =
      expUnit u1 * (r1 * expUnit u2 * r1⁻¹) * (t * (expUnit u3)⁻¹ * t⁻¹) * (t' * (expUnit u4)⁻¹ * t'⁻¹) * t' := by
    rw [plaquetteHolonomy_eq]
    simp only [ht', ht, hr1, hr2, hr3, hr4, hu1, hu2, hu3, hu4]
    group
  set A2 := r1 * expUnit u2 * r1⁻¹ with hA2
  set A3 := t * (expUnit u3)⁻¹ * t⁻¹ with hA3
  set A4 := t' * (expUnit u4)⁻¹ * t'⁻¹ with hA4
  have n1 : ‖(expUnit u1 : ℍ[ℝ]) - 1‖ ≤ ‖(u1 : ℍ[ℝ])‖ := norm_coe_expUnit_sub_one_le _
  have n2 : ‖(A2 : ℍ[ℝ]) - 1‖ ≤ ‖(u2 : ℍ[ℝ])‖ := by
    rw [hA2, norm_coe_conj_sub_one]
    exact norm_coe_expUnit_sub_one_le _
  have n3 : ‖(A3 : ℍ[ℝ]) - 1‖ ≤ ‖(u3 : ℍ[ℝ])‖ := by
    rw [hA3, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    exact norm_coe_expUnit_sub_one_le _
  have n4 : ‖(A4 : ℍ[ℝ]) - 1‖ ≤ ‖(u4 : ℍ[ℝ])‖ := by
    rw [hA4, norm_coe_conj_sub_one, norm_coe_inv_sub_one]
    exact norm_coe_expUnit_sub_one_le _
  have d1 : linearDeviation (expUnit u1) (u1 : ℍ[ℝ]) ≤ 3 * ‖(u1 : ℍ[ℝ])‖ ^ 2 := linearDeviation_expUnit _
  have d2 : linearDeviation A2 (adjointAction r1 u2) ≤ 3 * ‖(u2 : ℍ[ℝ])‖ ^ 2 := by
    rw [hA2, linearDeviation_conj]
    exact linearDeviation_expUnit _
  have d3 : linearDeviation A3 (adjointAction t (-(u3 : ℍ[ℝ]))) ≤ 3 * ‖(u3 : ℍ[ℝ])‖ ^ 2 := by
    rw [hA3, linearDeviation_conj]
    exact linearDeviation_expUnit_inv _
  have d4 : linearDeviation A4 (adjointAction t' (-(u4 : ℍ[ℝ]))) ≤ 3 * ‖(u4 : ℍ[ℝ])‖ ^ 2 := by
    rw [hA4, linearDeviation_conj]
    exact linearDeviation_expUnit_inv _
  have hprod := linearDeviation_mul_four_le (expUnit u1) A2 A3 A4 (u1 : ℍ[ℝ]) (adjointAction r1 u2)
    (adjointAction t (-(u3 : ℍ[ℝ]))) (adjointAction t' (-(u4 : ℍ[ℝ])))
  have hcurl : (u1 : ℍ[ℝ]) + adjointAction r1 u2 + adjointAction t (-(u3 : ℍ[ℝ])) +
      adjointAction t' (-(u4 : ℍ[ℝ])) = linearizedCurl R u (x, μ, ν) := by
    simp only [linearizedCurl, adjointAction, ht, ht', mul_neg, neg_mul]
    abel
  rw [hcurl] at hprod
  set a := ‖(u1 : ℍ[ℝ])‖
  set b := ‖(u2 : ℍ[ℝ])‖
  set c := ‖(u3 : ℍ[ℝ])‖
  set d := ‖(u4 : ℍ[ℝ])‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have hc : 0 ≤ c := norm_nonneg _
  have hd : 0 ≤ d := norm_nonneg _
  have hs : (‖(expUnit u1 : ℍ[ℝ]) - 1‖ + ‖(A2 : ℍ[ℝ]) - 1‖ + ‖(A3 : ℍ[ℝ]) - 1‖ + ‖(A4 : ℍ[ℝ]) - 1‖) ^ 2 ≤
      (a + b + c + d) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have hdev : ‖((expUnit u1 * A2 * A3 * A4 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ ‖linearizedCurl R u (x, μ, ν)‖ +
      4 * (a + b + c + d) ^ 2 := by
    have h1 : ‖((expUnit u1 * A2 * A3 * A4 : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤
        linearDeviation (expUnit u1 * A2 * A3 * A4) (linearizedCurl R u (x, μ, ν)) +
          ‖linearizedCurl R u (x, μ, ν)‖ := by
      unfold linearDeviation
      have := norm_add_le (((expUnit u1 * A2 * A3 * A4 : UnitQuaternion) : ℍ[ℝ]) - 1 - linearizedCurl R u (x, μ, ν))
        (linearizedCurl R u (x, μ, ν))
      simpa using this
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d, mul_nonneg ha hb, mul_nonneg ha hc,
      mul_nonneg ha hd, mul_nonneg hb hc, mul_nonneg hb hd, mul_nonneg hc hd]
  rw [hg]
  have hfin := norm_coe_mul_sub_one_le (expUnit u1 * A2 * A3 * A4) t'
  have hcv : plaquetteDefect R (x, μ, ν) = ‖(t' : ℍ[ℝ]) - 1‖ := by
    unfold plaquetteDefect
    rw [hR]
  rw [hcv]
  show ‖((expUnit u1 * A2 * A3 * A4 * t' : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ _
  linarith
theorem gaugedBlockFit_le {j : ℕ} (X : F.GaugeField j) (k : F.Site (j + 1) → UnitQuaternion)
    (X' : F.GaugeField (j + 1)) (c : F.Site (j + 1) × Fin 4) (h1 : ‖gaugedContourAverage X k c‖ ≤ 1) :
    gaugedBlockFit X k X' c ≤
      ‖((X' c.1 c.2 * (polarUnit (gaugedContourAverage X k c))⁻¹ : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by
  set q := gaugedContourAverage X k c with hq
  set m := X' c.1 c.2 * (polarUnit q)⁻¹ with hm
  have hsq := norm_coe_sub_one_sq m
  unfold gaugedBlockFit
  rw [← hq]
  by_cases h0 : q = 0
  · rw [h0]
    simp only [norm_zero, zero_mul, Quaternion.re_zero, sub_zero]
    positivity
  · have hu : q = ‖q‖ • ((polarUnit q : UnitQuaternion) : ℍ[ℝ]) := by
      rw [coe_polarUnit h0, smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 h0), one_smul]
    have hinv : polarUnit q * (X' c.1 c.2)⁻¹ = m⁻¹ := by
      rw [hm]
      group
    have hre : (q * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ])).re = ‖q‖ * (m : ℍ[ℝ]).re := by
      have e : q * (((X' c.1 c.2)⁻¹ : UnitQuaternion) : ℍ[ℝ]) = ‖q‖ • ((m⁻¹ : UnitQuaternion) : ℍ[ℝ]) := by
        rw [← hinv, coe_mul_unitQuaternion]
        conv_lhs => rw [hu]
        rw [smul_mul_assoc]
      rw [e, coe_unitQuaternion_inv]
      simp
    rw [hre, hsq]
    nlinarith
theorem norm_contourAverage_le_one {j : ℕ} (hL : Odd F.blockSide) (X : F.GaugeField j)
    (c : F.Site (j + 1) × Fin 4) : ‖contourAverage X c‖ ≤ 1 := by apply _root_.YangMills.Construction.BlockAverages.VariationRates.norm_contourAverage_le_one <;> assumption
theorem norm_gaugedContourAverage_le_one {j : ℕ} (hL : Odd F.blockSide) (X : F.GaugeField j)
    (k : F.Site (j + 1) → UnitQuaternion) (c : F.Site (j + 1) × Fin 4) : ‖gaugedContourAverage X k c‖ ≤ 1 := by
  unfold gaugedContourAverage
  rw [norm_mul, norm_mul, norm_coe_unitQuaternion, norm_coe_unitQuaternion, one_mul, mul_one]
  exact norm_contourAverage_le_one hL X c
theorem plaquetteEnergy_eq (X : F.GaugeField 0) (p : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteEnergy X p = ‖((plaquetteHolonomy X p : UnitQuaternion) : ℍ[ℝ]) - 1‖ ^ 2 / 2 := by apply _root_.YangMills.Construction.HoleFilling.plaquetteEnergy_eq <;> assumption
theorem sum_comp_le_mul_sum_of_card_fiber_le {A B : Type} [DecidableEq B] (P : Finset A) (Q : Finset B)
    (φ : A → B) (f : B → ℝ) (hf : ∀ x, 0 ≤ f x) (K : ℕ) (hmap : ∀ p ∈ P, φ p ∈ Q)
    (hfib : ∀ b, (P.filter fun p => φ p = b).card ≤ K) :
    ∑ p ∈ P, f (φ p) ≤ K * ∑ x ∈ Q, f x := by
  classical
  have := LumpContours.BlockLevels.sum_sum_le_mul_sum_of_card_le P (fun p => ({φ p} : Finset B)) Q f hf K
    (fun p hp => Finset.singleton_subset_iff.2 (hmap p hp))
    (fun x _ => by
      have e : (P.filter fun p => x ∈ ({φ p} : Finset B)) = P.filter fun p => φ p = x := by
        ext p
        simp [eq_comm]
      rw [e]
      exact hfib x)
  simpa using this
theorem enclosingCell_corner_mem_cellBall_three (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    {S : Finset F.Cell} {z : F.Cell} {p : F.Site 0 × Fin 4 × Fin 4} (hp : p ∈ plaquettesOver S {z} 0)
    {x : F.Site 0} (hx : x ∈ plaquetteCorners p) :
    enclosingCell x ∈ cellBall S z 3 := by
  classical
  simp only [plaquettesOver, innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
    Finset.mem_singleton] at hp
  obtain ⟨⟨-, h2, h3⟩, h4⟩ := hp
  have hb := LumpContours.BlockLevels.enclosingCell_corner_mem_cellBall (Nat.zero_le _) hL.pos p h2 hx
  rw [h4] at hb
  refine Finset.mem_filter.2
    ⟨LumpContours.BlockLevels.enclosingCell_mem_of_mem_sitesOfCells (Nat.zero_le _) hL (h3 hx), ?_⟩
  obtain ⟨h, hh, e⟩ := Finset.mem_image.1 hb
  rw [← e, BlockLines.cellSupDist_comm]
  have hd := cellSupDist_add_le hamb z (a := h) (r := 1) (by norm_num) (fun i => by
    have := LumpContours.BlockLevels.mem_centredCube_iff.1 hh i
    simpa using this)
  omega
theorem add_four_pow_four_le (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    (a + b + c + d) ^ 4 ≤ 64 * (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) := by
  have h2 : ∀ x y : ℝ, (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := fun x y => by nlinarith [sq_nonneg (x - y)]
  have s1 := h2 (a + b) (c + d)
  have s2 := h2 a b
  have s3 := h2 c d
  have s4 : (a + b + c + d) ^ 2 ≤ 4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by nlinarith
  have s5 : ((a + b + c + d) ^ 2) ^ 2 ≤ (4 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) s4 2
  have s6 := h2 (a ^ 2 + b ^ 2) (c ^ 2 + d ^ 2)
  have s7 := h2 (a ^ 2) (b ^ 2)
  have s8 := h2 (c ^ 2) (d ^ 2)
  nlinarith
theorem plaquetteEnergy_chart_le (R : F.GaugeField 0) (u : F.Site 0 → Fin 4 → imaginaryQuaternions)
    (p : F.Site 0 × Fin 4 × Fin 4) :
    plaquetteEnergy (fun x i => expUnit (u x i) * R x i) p ≤
      (3 / 2) * ‖linearizedCurl R u p‖ ^ 2 + (3 / 2) * plaquetteDefect R p ^ 2 +
        1536 * (‖(u p.1 p.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(u (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ ^ 4 +
          ‖(u (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ ^ 4 + ‖(u p.1 p.2.2 : ℍ[ℝ])‖ ^ 4) := by
  rw [plaquetteEnergy_eq]
  have h := norm_plaquetteHolonomy_chart_sub_one_le R u p
  set D := ‖linearizedCurl R u p‖
  set K := plaquetteDefect R p
  set a := ‖(u p.1 p.2.1 : ℍ[ℝ])‖ with ha
  set b := ‖(u (p.1 + unitStep 0 p.2.1) p.2.2 : ℍ[ℝ])‖ with hb
  set c := ‖(u (p.1 + unitStep 0 p.2.2) p.2.1 : ℍ[ℝ])‖ with hc
  set d := ‖(u p.1 p.2.2 : ℍ[ℝ])‖ with hd
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hc0 : 0 ≤ c := norm_nonneg _
  have hd0 : 0 ≤ d := norm_nonneg _
  have h4 := add_four_pow_four_le a b c d ha0 hb0 hc0 hd0
  set E := ‖((plaquetteHolonomy (fun x i => expUnit (u x i) * R x i) p : UnitQuaternion) : ℍ[ℝ]) - 1‖
  have hE : 0 ≤ E := norm_nonneg _
  set Q := (a + b + c + d) ^ 2 with hQ
  have h2 : E ^ 2 ≤ (D + K + 4 * Q) ^ 2 := pow_le_pow_left₀ hE h 2
  have h3 : (D + K + 4 * Q) ^ 2 ≤ 3 * (D ^ 2 + K ^ 2 + 16 * Q ^ 2) := by
    nlinarith [sq_nonneg (D - K), sq_nonneg (D - 4 * Q), sq_nonneg (K - 4 * Q)]
  have h5 : Q ^ 2 = (a + b + c + d) ^ 4 := by rw [hQ]; ring
  nlinarith
theorem sum_plaquetteEnergy_over_cell_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (S : Finset F.Cell) (z : F.Cell) (hz : z ∈ S) (R : F.FieldChain) (U : ChainChart F) (κ : ℝ) (hκ : 0 ≤ κ)
    (hcurv : ∀ p ∈ innerPlaquettes S 0, plaquetteDefect (R 0) p ≤ κ * levelScale F 0 ^ 2) :
    ∑ p ∈ plaquettesOver S {z} 0, plaquetteEnergy (chartField R U 0) p ≤
      (3 / 2) * unweightedLocalNorm S R U z ^ 2 + 1944 * κ ^ 2 + 24576 * unweightedLocalNorm S R U z ^ 4 := by
  classical
  obtain ⟨p1, p2, -⟩ := LocalNorms.unweightedLocalNorm_parts_le S R U z
  set P := plaquettesOver S {z} 0 with hP
  set Q := bondsOver S (cellBall S z 3) 0 with hQ
  set f : F.Site 0 × Fin 4 → ℝ := fun b => ‖(U.fine b.1 b.2 : ℍ[ℝ])‖ ^ 4 with hf
  have hf0 : ∀ b, 0 ≤ f b := fun b => by positivity
  have hz3 : z ∈ cellBall S z 3 := Finset.mem_filter.2 ⟨hz, by rw [BlockLines.cellSupDist_self]; omega⟩
  have hPmem : ∀ p ∈ P, p.2.1 < p.2.2 ∧ plaquetteCorners p ⊆ sitesOfCells S 0 ∧ enclosingCell p.1 = z ∧
      p ∈ innerPlaquettes S 0 := by
    intro p hp
    have h := hp
    simp only [hP, plaquettesOver, innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true,
      Finset.mem_singleton] at h
    refine ⟨h.1.2.1, h.1.2.2, h.2, ?_⟩
    simp only [innerPlaquettes, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact h.1
  have hbond : ∀ p ∈ P, ∀ x i, x ∈ plaquetteCorners p → x + unitStep 0 i ∈ plaquetteCorners p → (x, i) ∈ Q := by
    intro p hp x i h1 h2
    obtain ⟨-, hc, -, -⟩ := hPmem p hp
    refine Finset.mem_filter.2 ⟨?_, enclosingCell_corner_mem_cellBall_three hamb hL hp h1⟩
    simp only [innerBonds, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
    exact ⟨hc h1, hc h2⟩
  have c1 : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.1 ∈ plaquetteCorners p := fun p => by simp [plaquetteCorners]
  have c2 : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.1 + unitStep 0 p.2.1 ∈ plaquetteCorners p :=
    fun p => by simp [plaquetteCorners]
  have c3 : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p :=
    fun p => by simp [plaquetteCorners]
  have c4 : ∀ p : F.Site 0 × Fin 4 × Fin 4, p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 ∈ plaquetteCorners p :=
    fun p => by simp [plaquetteCorners]
  have fib : ∀ (φ : F.Site 0 × Fin 4 × Fin 4 → F.Site 0 × Fin 4) (g : F.Site 0 × Fin 4 × Fin 4 → Fin 4),
      (∀ p p', φ p = φ p' → g p = g p' → p = p') → ∀ b, (P.filter fun p => φ p = b).card ≤ 4 := by
    intro φ g hinj b
    have := Finset.card_le_card_of_injOn (s := P.filter fun p => φ p = b) (t := (Finset.univ : Finset (Fin 4))) g
      (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
      (fun p hp p' hp' h => hinj p p' ((Finset.mem_filter.1 hp).2.trans (Finset.mem_filter.1 hp').2.symm) h)
    simpa using this
  have s1 : ∑ p ∈ P, f (p.1, p.2.1) ≤ 4 * ∑ b ∈ Q, f b := by
    have := sum_comp_le_mul_sum_of_card_fiber_le P Q (fun p => (p.1, p.2.1)) f hf0 4
      (fun p hp => hbond p hp _ _ (c1 p) (c2 p))
      (fib _ (fun p => p.2.2) (fun ⟨x, μ, ν⟩ ⟨x', μ', ν'⟩ h1 h2 => by
        simp only [Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨h1.1, h1.2, h2⟩))
    simpa using this
  have s2 : ∑ p ∈ P, f (p.1 + unitStep 0 p.2.1, p.2.2) ≤ 4 * ∑ b ∈ Q, f b := by
    have := sum_comp_le_mul_sum_of_card_fiber_le P Q (fun p => (p.1 + unitStep 0 p.2.1, p.2.2)) f hf0 4
      (fun p hp => hbond p hp _ _ (c2 p) (c4 p))
      (fib _ (fun p => p.2.1) (fun ⟨x, μ, ν⟩ ⟨x', μ', ν'⟩ h1 h2 => by
        simp only [Prod.mk.injEq] at h1 h2 ⊢
        subst h2
        exact ⟨add_right_cancel h1.1, rfl, h1.2⟩))
    simpa using this
  have s3 : ∑ p ∈ P, f (p.1 + unitStep 0 p.2.2, p.2.1) ≤ 4 * ∑ b ∈ Q, f b := by
    have := sum_comp_le_mul_sum_of_card_fiber_le P Q (fun p => (p.1 + unitStep 0 p.2.2, p.2.1)) f hf0 4
      (fun p hp => hbond p hp _ _ (c3 p) (by
        have e : p.1 + unitStep 0 p.2.2 + unitStep 0 p.2.1 = p.1 + unitStep 0 p.2.1 + unitStep 0 p.2.2 := by abel
        rw [e]
        exact c4 p))
      (fib _ (fun p => p.2.2) (fun ⟨x, μ, ν⟩ ⟨x', μ', ν'⟩ h1 h2 => by
        simp only [Prod.mk.injEq] at h1 h2 ⊢
        subst h2
        exact ⟨add_right_cancel h1.1, h1.2, rfl⟩))
    simpa using this
  have s4 : ∑ p ∈ P, f (p.1, p.2.2) ≤ 4 * ∑ b ∈ Q, f b := by
    have := sum_comp_le_mul_sum_of_card_fiber_le P Q (fun p => (p.1, p.2.2)) f hf0 4
      (fun p hp => hbond p hp _ _ (c1 p) (c3 p))
      (fib _ (fun p => p.2.1) (fun ⟨x, μ, ν⟩ ⟨x', μ', ν'⟩ h1 h2 => by
        simp only [Prod.mk.injEq] at h1 h2 ⊢
        exact ⟨h1.1, h2, h1.2⟩))
    simpa using this
  have sD : ∑ p ∈ P, ‖linearizedCurl (R 0) U.fine p‖ ^ 2 ≤ unweightedLocalNorm S R U z ^ 2 := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity) p2
    intro p hp
    obtain ⟨-, -, hc, hpl⟩ := hPmem p hp
    exact Finset.mem_filter.2 ⟨hpl, by rw [hc]; exact hz3⟩
  have hz1 : z ∈ cellBall S z 1 := Finset.mem_filter.2 ⟨hz, by rw [BlockLines.cellSupDist_self]; omega⟩
  have hcard : (P.card : ℝ) ≤ 1296 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4 := by
    have hsub : P ⊆ sitesOfCells (cellBall S z 1) 0 ×ˢ (Finset.univ : Finset (Fin 4)) ×ˢ
        (Finset.univ : Finset (Fin 4)) := by
      intro p hp
      obtain ⟨-, hc, hcell, -⟩ := hPmem p hp
      simp only [Finset.mem_product, Finset.mem_univ, and_true]
      exact BlockLines.mem_sitesOfCells_of_enclosingCell_mem hL (hc (c1 p)) (by rw [hcell]; exact hz1)
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_product, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := BlockLines.card_sitesOfCells_le hL (cellBall S z 1) 0
    have h3 := BlockLines.card_cellBall_one_le S z
    have h4 : P.card ≤ 81 * (F.blockSide ^ (F.top - 0)) ^ 4 * 16 := by
      refine h1.trans ?_
      have : (cellBall S z 1).card * (F.blockSide ^ (F.top - 0)) ^ 4 ≤ 81 * (F.blockSide ^ (F.top - 0)) ^ 4 :=
        Nat.mul_le_mul_right _ h3
      nlinarith
    have h5 : (P.card : ℝ) ≤ ((81 * (F.blockSide ^ (F.top - 0)) ^ 4 * 16 : ℕ) : ℝ) := by exact_mod_cast h4
    refine h5.trans (le_of_eq ?_)
    push_cast
    ring
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have sK : ∑ p ∈ P, plaquetteDefect (R 0) p ^ 2 ≤ 1296 * κ ^ 2 := by
    have hone : levelScale F 0 ^ 4 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4 = 1 := by
      unfold levelScale
      rw [← mul_pow, ← mul_pow]
      simp [hL0.ne']
    have hK : ∀ p ∈ P, plaquetteDefect (R 0) p ^ 2 ≤ κ ^ 2 * levelScale F 0 ^ 4 := by
      intro p hp
      obtain ⟨-, -, -, hpl⟩ := hPmem p hp
      have h1 := hcurv p hpl
      have h2 : plaquetteDefect (R 0) p ^ 2 ≤ (κ * levelScale F 0 ^ 2) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc _ ≤ _ := h2
        _ = _ := by ring
    refine (Finset.sum_le_sum hK).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hl : 0 ≤ κ ^ 2 * levelScale F 0 ^ 4 := by
      unfold levelScale
      positivity
    calc (P.card : ℝ) * (κ ^ 2 * levelScale F 0 ^ 4) ≤
        (1296 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4) * (κ ^ 2 * levelScale F 0 ^ 4) :=
          mul_le_mul_of_nonneg_right hcard hl
      _ = 1296 * κ ^ 2 * (levelScale F 0 ^ 4 * ((F.blockSide : ℝ) ^ (F.top - 0)) ^ 4) := by ring
      _ = _ := by rw [hone, mul_one]
  have hterm : ∀ p ∈ P, plaquetteEnergy (chartField R U 0) p ≤
      (3 / 2) * ‖linearizedCurl (R 0) U.fine p‖ ^ 2 + (3 / 2) * plaquetteDefect (R 0) p ^ 2 +
        1536 * (f (p.1, p.2.1) + f (p.1 + unitStep 0 p.2.1, p.2.2) + f (p.1 + unitStep 0 p.2.2, p.2.1) +
          f (p.1, p.2.2)) := fun p _ => plaquetteEnergy_chart_le (R 0) U.fine p
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  have hQf : ∑ b ∈ Q, f b ≤ unweightedLocalNorm S R U z ^ 4 := p1
  linarith
theorem chartChain_of_lt_top (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) {j : ℕ}
    (hj : j < F.top) : chartChain R U V j = chartField R U j := by apply _root_.YangMills.Construction.BlockAverages.ChartCoordinates.chartChain_of_lt <;> assumption
theorem gaugedBlockFit_chart_le (hL : Odd F.blockSide) (R : F.FieldChain) (U : ChainChart F)
    (V : F.GaugeField F.top) {j : ℕ} (hj : j + 1 < F.top) (c : F.Site (j + 1) × Fin 4) :
    gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c ≤
      ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 + unitDeviation (referenceDefect R j c) ^ 2 := by
  rw [chartChain_of_lt_top R U V (show j < F.top by omega), chartChain_of_lt_top R U V hj]
  have h := gaugedBlockFit_le (chartField R U j) (chartGauge R U (j + 1)) (chartField R U (j + 1)) c
    (norm_gaugedContourAverage_le_one hL _ _ _)
  refine h.trans ?_
  have e : chartField R U (j + 1) c.1 c.2 *
      (polarUnit (gaugedContourAverage (chartField R U j) (chartGauge R U (j + 1)) c))⁻¹ =
      expUnit (U.coarse j c.1 c.2) * referenceDefect R j c := by
    show expUnit (U.coarse j c.1 c.2) * referenceDefect R j (c.1, c.2) *
      polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) (c.1, c.2)) *
      (polarUnit (gaugedContourAverage (chartField R U j) (balancingGauge (chartField R U j) (R j)) c))⁻¹ = _
    have hc' : ((c.1, c.2) : F.Site (j + 1) × Fin 4) = c := rfl
    rw [hc']
    group
  rw [e]
  have h1 := norm_coe_mul_sub_one_le (expUnit (U.coarse j c.1 c.2)) (referenceDefect R j c)
  have h2 := norm_coe_expUnit_sub_one_le (U.coarse j c.1 c.2)
  set A := ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖
  set B := unitDeviation (referenceDefect R j c)
  have h3 : ‖((expUnit (U.coarse j c.1 c.2) * referenceDefect R j c : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ A + B :=
    h1.trans (add_le_add_left h2 _)
  have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
  nlinarith [sq_nonneg (A - B)]
theorem sum_quarter_pow_le_one (t : ℕ) : ∑ j ∈ Finset.range t, ((1 : ℝ) / 4) ^ (t - j) ≤ 1 := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Finset.sum_range_succ]
    have e : ∑ j ∈ Finset.range t, ((1 : ℝ) / 4) ^ (t + 1 - j) =
        (1 / 4) * ∑ j ∈ Finset.range t, ((1 : ℝ) / 4) ^ (t - j) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      have hj' : j < t := Finset.mem_range.1 hj
      have : t + 1 - j = (t - j) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [e]
    have : t + 1 - t = 1 := by omega
    rw [this]
    norm_num
    linarith
theorem sum_referenceDefect_sq_over_cell_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide)
    (h2L : 2 ≤ F.blockSide) (S : Finset F.Cell) (z : F.Cell) (R : F.FieldChain) (κ : ℝ) (hκ : 0 ≤ κ)
    (hmis : ∀ j, j + 1 < F.top → ∀ c ∈ innerBonds S (j + 1),
      unitDeviation (referenceDefect R j c) ≤ κ * levelScale F (j + 1) ^ 3) :
    ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1), unitDeviation (referenceDefect R j c) ^ 2 ≤
      324 * κ ^ 2 := by
  classical
  have hL0 : (0 : ℝ) < F.blockSide := by exact_mod_cast hL.pos
  have hL2 : (2 : ℝ) ≤ F.blockSide := by exact_mod_cast h2L
  have hlev : ∀ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1),
      unitDeviation (referenceDefect R j c) ^ 2 ≤ 324 * κ ^ 2 * ((1 : ℝ) / 4) ^ (F.depth - j) := by
    intro j hj
    have hjt : j < F.depth := Finset.mem_range.1 hj
    have hjn : j + 1 < F.top := by
      show j + 1 < F.depth + 1
      omega
    set l := levelScale F (j + 1) with hl
    set M := (F.blockSide : ℝ) ^ (F.top - (j + 1)) with hM
    have hM0 : 0 < M := by positivity
    have hlM : l * M = 1 := by
      rw [hl, hM]
      unfold levelScale
      rw [← mul_pow]
      simp [hL0.ne']
    have hl0 : 0 ≤ l := by
      rw [hl]
      unfold levelScale
      positivity
    have hcard : ((bondsOver S {z} (j + 1)).card : ℝ) ≤ 324 * M ^ 4 := by
      have h1 : bondsOver S {z} (j + 1) ⊆ innerBonds (cellBall S z 1) (j + 1) := fun b hb =>
        BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hL S z (le_of_lt hjn) hb
      have h2 := (Finset.card_le_card h1).trans (BlockLines.card_innerBonds_le hL (cellBall S z 1) (j + 1))
      have h3 := BlockLines.card_cellBall_one_le S z
      have h4 : (bondsOver S {z} (j + 1)).card ≤ 4 * (81 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) := by
        refine h2.trans ?_
        exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h3)
      have h5 : ((bondsOver S {z} (j + 1)).card : ℝ) ≤
          ((4 * (81 * (F.blockSide ^ (F.top - (j + 1))) ^ 4) : ℕ) : ℝ) := by
        exact_mod_cast h4
      refine h5.trans (le_of_eq ?_)
      rw [hM]
      push_cast
      ring
    have hterm : ∀ c ∈ bondsOver S {z} (j + 1), unitDeviation (referenceDefect R j c) ^ 2 ≤ κ ^ 2 * l ^ 6 := by
      intro c hc
      have h1 := hmis j hjn c (Finset.mem_filter.1 hc).1
      have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      calc _ ≤ _ := h2
        _ = _ := by ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have h6 : 0 ≤ κ ^ 2 * l ^ 6 := by positivity
    have hll : l ^ 2 ≤ ((1 : ℝ) / 4) ^ (F.depth - j) := by
      have e : F.top - (j + 1) = F.depth - j := by
        show F.depth + 1 - (j + 1) = F.depth - j
        omega
      rw [hl]
      unfold levelScale
      rw [e, ← pow_mul, mul_comm, pow_mul]
      refine pow_le_pow_left₀ (by positivity) ?_ _
      rw [div_pow, one_pow]
      exact one_div_le_one_div_of_le (by norm_num) (by nlinarith)
    calc ((bondsOver S {z} (j + 1)).card : ℝ) * (κ ^ 2 * l ^ 6) ≤ (324 * M ^ 4) * (κ ^ 2 * l ^ 6) :=
          mul_le_mul_of_nonneg_right hcard h6
      _ = 324 * κ ^ 2 * ((l * M) ^ 4 * l ^ 2) := by ring
      _ = 324 * κ ^ 2 * l ^ 2 := by rw [hlM]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hll (by positivity)
  refine (Finset.sum_le_sum hlev).trans ?_
  rw [← Finset.mul_sum]
  have := sum_quarter_pow_le_one F.depth
  nlinarith [sq_nonneg κ]
theorem sum_coarse_sq_over_cell_le (S : Finset F.Cell) (z : F.Cell) (hz : z ∈ S) (R : F.FieldChain)
    (U : ChainChart F) :
    ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 ≤
      unweightedLocalNorm S R U z ^ 2 := by
  classical
  obtain ⟨-, -, p3⟩ := LocalNorms.unweightedLocalNorm_parts_le S R U z
  have hn : F.top - 1 = F.depth := by simp [BlockFrame.top]
  rw [hn] at p3
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) p3
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun _ _ _ => by positivity
  intro c hc
  obtain ⟨h1, h2⟩ := Finset.mem_filter.1 hc
  refine Finset.mem_filter.2 ⟨h1, ?_⟩
  rw [Finset.mem_singleton.1 h2]
  exact Finset.mem_filter.2 ⟨hz, by rw [BlockLines.cellSupDist_self]; omega⟩
theorem sum_top_gaugedBlockFit_le (hamb : IsAdmissibleAmbient F) (hL : Odd F.blockSide) (S : Finset F.Cell)
    (z : F.Cell) (R : F.FieldChain) (U : ChainChart F) (V : F.GaugeField F.top) (κ : ℝ) (hκ : 0 ≤ κ)
    (hg : ∀ c ∈ bondsOver S {z} F.top, normSubOne (chartBondMisfit R U V F.depth c) ≤ κ) :
    ∑ c ∈ bondsOver S {z} (F.depth + 1),
      gaugedBlockFit (chartChain R U V F.depth) (chartGauge R U (F.depth + 1))
        (chartChain R U V (F.depth + 1)) c ≤ 162 * κ ^ 2 := by
  classical
  have hterm : ∀ c ∈ bondsOver S {z} (F.depth + 1),
      gaugedBlockFit (chartChain R U V F.depth) (chartGauge R U (F.depth + 1))
        (chartChain R U V (F.depth + 1)) c ≤ κ ^ 2 / 2 := by
    intro c hc
    refine (gaugedBlockFit_le _ _ _ c (norm_gaugedContourAverage_le_one hL _ _ _)).trans ?_
    have h1 := hg c hc
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    exact div_le_div_of_nonneg_right h2 (by norm_num)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  have h1 : bondsOver S {z} (F.depth + 1) ⊆ innerBonds (cellBall S z 1) (F.depth + 1) := fun b hb =>
    BlockLines.mem_innerBonds_cellBall_of_mem_bondsOver hamb hL S z le_rfl hb
  have h2 := (Finset.card_le_card h1).trans (BlockLines.card_innerBonds_le hL (cellBall S z 1) (F.depth + 1))
  have h3 := BlockLines.card_cellBall_one_le S z
  have h0 : F.top - (F.depth + 1) = 0 := by simp [BlockFrame.top]
  rw [h0] at h2
  have h4 : (bondsOver S {z} (F.depth + 1)).card ≤ 324 := by
    refine h2.trans ?_
    simp only [pow_zero, one_pow, mul_one]
    omega
  have h5 : ((bondsOver S {z} (F.depth + 1)).card : ℝ) ≤ 324 := by exact_mod_cast h4
  nlinarith [sq_nonneg κ]
theorem cellTerms_arith (a C0 C1 r b w A T1 T2 : ℝ) (ha : 0 < a) (hr : 0 < r) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hw : r + b ≤ w) (hA : A ≤ (3 / 2) * b ^ 2 + 1944 * (C0 * r) ^ 2 + 24576 * b ^ 4)
    (hT1 : T1 ≤ b ^ 2 + 324 * (C0 * r) ^ 2) (hT2 : T2 ≤ 162 * (C1 * (r + b)) ^ 2) :
    A + a * (T1 + T2) ≤ (24578 + 1944 * C0 ^ 2 + a * (1 + 324 * C0 ^ 2 + 162 * C1 ^ 2)) * w ^ 2 := by
  have hb2 : b ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hb0 (by linarith) 2
  have hr2 : r ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ hr.le (by linarith) 2
  have hrb : (r + b) ^ 2 ≤ w ^ 2 := pow_le_pow_left₀ (by positivity) hw 2
  have hb21 : b ^ 2 ≤ 1 := pow_le_one₀ hb0 hb1
  have hb4 : b ^ 4 ≤ b ^ 2 := by
    have e : b ^ 4 = b ^ 2 * b ^ 2 := by ring
    rw [e]
    exact mul_le_of_le_one_right (sq_nonneg b) hb21
  have q0 : (C0 * r) ^ 2 ≤ C0 ^ 2 * w ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hr2 (sq_nonneg _)
  have q1 : (C1 * (r + b)) ^ 2 ≤ C1 ^ 2 * w ^ 2 := by
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hrb (sq_nonneg _)
  have hw2 : 0 ≤ w ^ 2 := sq_nonneg _
  have hA' : A ≤ (24578 + 1944 * C0 ^ 2) * w ^ 2 := by
    have e : (24578 + 1944 * C0 ^ 2) * w ^ 2 = 24578 * w ^ 2 + 1944 * (C0 ^ 2 * w ^ 2) := by ring
    rw [e]
    linarith
  have hT : T1 + T2 ≤ (1 + 324 * C0 ^ 2 + 162 * C1 ^ 2) * w ^ 2 := by
    have e : (1 + 324 * C0 ^ 2 + 162 * C1 ^ 2) * w ^ 2 =
        w ^ 2 + 324 * (C0 ^ 2 * w ^ 2) + 162 * (C1 ^ 2 * w ^ 2) := by
      ring
    rw [e]
    linarith
  have h3 := mul_le_mul_of_nonneg_left hT ha.le
  calc _ ≤ (24578 + 1944 * C0 ^ 2) * w ^ 2 + a * ((1 + 324 * C0 ^ 2 + 162 * C1 ^ 2) * w ^ 2) :=
        add_le_add hA' h3
    _ = _ := by ring
theorem smallCellTerms (hB : referenceBoundsStatement) (hM : topMisfitNearCellStatement) :
    smallCellTermsStatement := by
  obtain ⟨C0, c0, L1, hC0, hc0, hB⟩ := hB
  obtain ⟨C1, hC1, L2, hM⟩ := hM
  intro a ha
  refine ⟨24578 + 1944 * C0 ^ 2 + a * (1 + 324 * C0 ^ 2 + 162 * C1 ^ 2), by positivity,
    max (max L1 L2) 3, ?_⟩
  intro L hLo hLL del hdel
  have hL1 : L1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have hL2 : L2 ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have hL3 : 3 ≤ L := (le_max_right _ _).trans hLL
  obtain ⟨c2, hc2, hM2⟩ := hM L hLo hL2
  have hexp : 1 ≤ Real.exp (3 * del) := Real.one_le_exp (by positivity)
  set e3 := Real.exp (3 * del) with he3
  have he30 : 0 < e3 := by linarith
  set cm := min (min c0 c2) 1 with hcm
  have hcm0 : 0 < cm := lt_min (lt_min hc0 hc2) one_pos
  refine ⟨cm / e3, by positivity, ?_⟩
  intro F m S hF hamb hm hreg r V hr hrc hcold U hU β z hz hβ hbox
  subst hF
  have hcmle : cm / e3 ≤ cm := div_le_self hcm0.le hexp
  have hrc0 : r ≤ c0 := hrc.trans (hcmle.trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hrc2 : r ≤ c2 := hrc.trans (hcmle.trans ((min_le_left _ _).trans (min_le_right _ _)))
  set R := referenceFieldChain S V with hR
  set b := unweightedLocalNorm S R U z with hb
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have hbβ : b ≤ β := hbox z (Finset.mem_filter.2 ⟨hz, by rw [BlockLines.cellSupDist_self]; omega⟩)
  have hbs : b ≤ cm := by
    have h1 := LocalNorms.unweightedLocalNorm_le_exp_mul_supWeightedNorm del hdel S R U z hz
    have h2 : e3 * supWeightedNorm S del R U ≤ e3 * (cm / e3) := mul_le_mul_of_nonneg_left hU he30.le
    have h3 : e3 * (cm / e3) = cm := by field_simp
    linarith
  have hb1 : b ≤ 1 := hbs.trans (min_le_right _ _)
  have hbc2 : b ≤ c2 := hbs.trans ((min_le_left _ _).trans (min_le_right _ _))
  obtain ⟨-, b2, b3, -, -, -⟩ := hB F m S hLo hL1 hamb hm hreg r V hr hrc0 hcold
  have hκ0 : 0 ≤ C0 * r := by positivity
  have hA := sum_plaquetteEnergy_over_cell_le hamb hLo S z hz R U (C0 * r) hκ0
    (fun p hp => b2 0 (Nat.succ_pos _) p hp)
  have hE := sum_referenceDefect_sq_over_cell_le hamb hLo (by omega) S z R (C0 * r) hκ0
    (fun j hj c hc => b3 j hj c hc)
  have hU2 := sum_coarse_sq_over_cell_le S z hz R U
  have hmid : ∑ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1),
      gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c ≤
      b ^ 2 + 324 * (C0 * r) ^ 2 := by
    have h1 : ∀ j ∈ Finset.range F.depth, ∑ c ∈ bondsOver S {z} (j + 1),
        gaugedBlockFit (chartChain R U V j) (chartGauge R U (j + 1)) (chartChain R U V (j + 1)) c ≤
        ∑ c ∈ bondsOver S {z} (j + 1), ‖(U.coarse j c.1 c.2 : ℍ[ℝ])‖ ^ 2 +
          ∑ c ∈ bondsOver S {z} (j + 1), unitDeviation (referenceDefect R j c) ^ 2 := by
      intro j hj
      have hjt : j < F.depth := Finset.mem_range.1 hj
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun c _ => gaugedBlockFit_chart_le hLo R U V (show j + 1 < F.depth + 1 by omega) c
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib]
    linarith
  have hmis : ∀ c ∈ bondsOver S {z} F.top, normSubOne (chartBondMisfit R U V F.depth c) ≤ C1 * (r + b) :=
    hM2 F m S rfl hamb hm hreg r V hr hrc2 hcold U z b hz hb0 hbc2 le_rfl
  have htop := sum_top_gaugedBlockFit_le hamb hLo S z R U V (C1 * (r + b)) (by positivity) hmis
  unfold chartCellTerms cellTerms
  rw [chartChain_of_lt_top R U V (Nat.succ_pos _), show Finset.range F.top = Finset.range (F.depth + 1) from rfl,
    Finset.sum_range_succ]
  exact cellTerms_arith a C0 C1 r b (r + β) _ _ _ ha hr hb0 hb1 (by linarith) hA hmid htop
end SmallCellTerms
end YangMills.Construction
end
