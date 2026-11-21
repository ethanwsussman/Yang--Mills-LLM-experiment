import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open NormedSpace
namespace YangMills.Construction
namespace QuaternionLog
local instance instNormedAlgebraRatQuaternion : NormedAlgebra ℚ ℍ[ℝ] := NormedAlgebra.restrictScalars ℚ ℝ ℍ[ℝ]
theorem contDiffAt_exp_zero : ContDiffAt ℝ 3 (exp : ℍ[ℝ] → ℍ[ℝ]) 0 :=
  (exp_analytic (𝕂 := ℝ) (0 : ℍ[ℝ])).contDiffAt
theorem hasFDerivAt_exp_zero_refl :
    HasFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ]) ((ContinuousLinearEquiv.refl ℝ ℍ[ℝ] : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 :=
  hasFDerivAt_exp_zero (𝕂 := ℝ)
theorem hasStrictFDerivAt_exp_zero_refl : HasStrictFDerivAt (exp : ℍ[ℝ] → ℍ[ℝ])
    ((ContinuousLinearEquiv.refl ℝ ℍ[ℝ] : ℍ[ℝ] ≃L[ℝ] ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 0 :=
  hasStrictFDerivAt_exp_zero (𝕂 := ℝ)
def qlog : ℍ[ℝ] → ℍ[ℝ] := contDiffAt_exp_zero.localInverse hasFDerivAt_exp_zero_refl (by norm_num)
theorem exp_zero_eq_one : (exp (0 : ℍ[ℝ]) : ℍ[ℝ]) = 1 := exp_zero
theorem contDiffAt_qlog_one : ContDiffAt ℝ 3 qlog 1 := by
  have := contDiffAt_exp_zero.to_localInverse hasFDerivAt_exp_zero_refl (by norm_num)
  rwa [exp_zero_eq_one] at this
theorem hasStrictFDerivAt_qlog_one : HasStrictFDerivAt qlog (1 : ℍ[ℝ] →L[ℝ] ℍ[ℝ]) 1 := by
  have := hasStrictFDerivAt_exp_zero_refl.to_localInverse
  rw [exp_zero_eq_one] at this
  exact this
theorem eventually_qlog_exp : ∀ᶠ q in nhds (0 : ℍ[ℝ]), qlog (exp q) = q :=
  hasStrictFDerivAt_exp_zero_refl.eventually_left_inverse
theorem eventually_exp_qlog : ∀ᶠ g in nhds (1 : ℍ[ℝ]), exp (qlog g) = g := by
  have := hasStrictFDerivAt_exp_zero_refl.eventually_right_inverse
  rw [exp_zero_eq_one] at this
  exact this
theorem qlog_one : qlog 1 = 0 := by
  have := hasStrictFDerivAt_exp_zero_refl.localInverse_apply_image
  rw [exp_zero_eq_one] at this
  exact this
theorem eventually_contDiffAt_qlog : ∀ᶠ g in nhds (1 : ℍ[ℝ]), ContDiffAt ℝ 3 qlog g :=
  contDiffAt_qlog_one.eventually (by simp)
def unitConj (h : ℍ[ℝ]) (q : ℍ[ℝ]) : ℍ[ℝ] := h * q * star h
theorem star_mul_self_of_norm_eq_one {h : ℍ[ℝ]} (hh : ‖h‖ = 1) : star h * h = 1 := by
  rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, hh]
  simp
theorem mul_star_self_of_norm_eq_one {h : ℍ[ℝ]} (hh : ‖h‖ = 1) : h * star h = 1 := by
  rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, hh]
  simp
theorem norm_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) (q : ℍ[ℝ]) : ‖unitConj h q‖ = ‖q‖ := by
  simp [unitConj, norm_mul, hh]
theorem exp_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) (q : ℍ[ℝ]) : exp (unitConj h q) = unitConj h (exp q) := by
  let y : (ℍ[ℝ])ˣ := ⟨h, star h, mul_star_self_of_norm_eq_one hh, star_mul_self_of_norm_eq_one hh⟩
  exact exp_units_conj y q
structure QlogRadii (ρ r : ℝ) : Prop where
  left_pos : 0 < ρ
  right_pos : 0 < r
  qlog_exp : ∀ q : ℍ[ℝ], ‖q‖ < ρ → qlog (exp q) = q
  exp_qlog : ∀ g : ℍ[ℝ], ‖g - 1‖ < r → exp (qlog g) = g
  norm_qlog_lt : ∀ g : ℍ[ℝ], ‖g - 1‖ < r → ‖qlog g‖ < ρ
  contDiffAt : ∀ g : ℍ[ℝ], ‖g - 1‖ < r → ContDiffAt ℝ 3 qlog g
theorem exists_qlogRadii : ∃ ρ r : ℝ, QlogRadii ρ r := by
  obtain ⟨ρ, hρ, h1⟩ := Metric.eventually_nhds_iff.1 eventually_qlog_exp
  have hc : Filter.Tendsto qlog (nhds 1) (nhds 0) := by
    have := hasStrictFDerivAt_qlog_one.hasFDerivAt.continuousAt.tendsto
    rwa [qlog_one] at this
  have h2 : ∀ᶠ g in nhds (1 : ℍ[ℝ]), ‖qlog g‖ < ρ := by
    have := hc.eventually (Metric.ball_mem_nhds (0 : ℍ[ℝ]) hρ)
    filter_upwards [this] with g hg
    simpa using hg
  obtain ⟨r, hr, h3⟩ := Metric.eventually_nhds_iff.1 (eventually_exp_qlog.and (h2.and eventually_contDiffAt_qlog))
  refine ⟨ρ, r, hρ, hr, fun q hq => h1 (by simpa using hq), fun g hg => (h3 (by simpa [dist_eq_norm] using hg)).1,
    fun g hg => (h3 (by simpa [dist_eq_norm] using hg)).2.1, fun g hg => (h3 (by simpa [dist_eq_norm] using hg)).2.2⟩
def leftRadius : ℝ := exists_qlogRadii.choose
def rightRadius : ℝ := exists_qlogRadii.choose_spec.choose
theorem qlogRadii_spec : QlogRadii leftRadius rightRadius := exists_qlogRadii.choose_spec.choose_spec
theorem qlog_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) {g : ℍ[ℝ]} (hg : ‖g - 1‖ < rightRadius) :
    qlog (unitConj h g) = unitConj h (qlog g) := by
  have h1 := qlogRadii_spec.qlog_exp (unitConj h (qlog g))
    (by rw [norm_unitConj hh]; exact qlogRadii_spec.norm_qlog_lt g hg)
  rw [exp_unitConj hh, qlogRadii_spec.exp_qlog g hg] at h1
  exact h1
theorem norm_unitConj_sub_one {h : ℍ[ℝ]} (hh : ‖h‖ = 1) (g : ℍ[ℝ]) : ‖unitConj h g - 1‖ = ‖g - 1‖ := by
  have : unitConj h g - 1 = unitConj h (g - 1) := by
    simp [unitConj, mul_sub, sub_mul, mul_star_self_of_norm_eq_one hh]
  rw [this, norm_unitConj hh]
def rightTransDeriv (q a : ℍ[ℝ]) : ℍ[ℝ] := fderiv ℝ qlog (exp q) (a * exp q)
def rightTransDerivCLM (q : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  (fderiv ℝ qlog (exp q)).comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (exp q))
theorem rightTransDerivCLM_apply (q a : ℍ[ℝ]) : rightTransDerivCLM q a = rightTransDeriv q a := rfl
theorem eventually_norm_exp_sub_one_lt : ∀ᶠ q in nhds (0 : ℍ[ℝ]), ‖exp q - 1‖ < rightRadius := by
  have hc : Filter.Tendsto (exp : ℍ[ℝ] → ℍ[ℝ]) (nhds 0) (nhds 1) := by
    have := (exp_analytic (𝕂 := ℝ) (0 : ℍ[ℝ])).continuousAt.tendsto
    rwa [exp_zero_eq_one] at this
  have := hc.eventually (Metric.ball_mem_nhds (1 : ℍ[ℝ]) qlogRadii_spec.right_pos)
  filter_upwards [this] with g hg
  simpa [dist_eq_norm] using hg
theorem contDiffAt_rightTransDerivCLM : ContDiffAt ℝ 2 rightTransDerivCLM 0 := by
  have h1 : ContDiffAt ℝ 2 (fderiv ℝ qlog) (exp (0 : ℍ[ℝ])) := by
    rw [exp_zero_eq_one]
    exact contDiffAt_qlog_one.fderiv_right (by norm_num)
  have he : ContDiffAt ℝ 2 (exp : ℍ[ℝ] → ℍ[ℝ]) 0 := (exp_analytic (𝕂 := ℝ) (0 : ℍ[ℝ])).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun q : ℍ[ℝ] => fderiv ℝ qlog (exp q)) 0 := h1.comp 0 he
  have h3 : ContDiffAt ℝ 2 (fun q : ℍ[ℝ] => (ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (exp q)) 0 :=
    ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip.contDiff.contDiffAt).comp 0 he
  exact h2.clm_comp h3
theorem rightTransDerivCLM_zero : rightTransDerivCLM 0 = 1 := by
  refine ContinuousLinearMap.ext fun a => ?_
  simp only [rightTransDerivCLM, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.mul_apply', exp_zero_eq_one, mul_one]
  rw [hasStrictFDerivAt_qlog_one.hasFDerivAt.fderiv]
theorem contDiffAt_rightTransDeriv (a : ℍ[ℝ]) : ContDiffAt ℝ 2 (fun q => rightTransDeriv q a) 0 := by
  have := contDiffAt_rightTransDerivCLM.clm_apply (contDiffAt_const (c := a))
  exact this
theorem rightTransDeriv_zero (a : ℍ[ℝ]) : rightTransDeriv 0 a = a := by
  rw [← rightTransDerivCLM_apply, rightTransDerivCLM_zero]
  rfl
theorem rightTransDeriv_add (q a b : ℍ[ℝ]) :
    rightTransDeriv q (a + b) = rightTransDeriv q a + rightTransDeriv q b := by
  simp only [← rightTransDerivCLM_apply, map_add]
theorem rightTransDeriv_smul (q : ℍ[ℝ]) (r : ℝ) (a : ℍ[ℝ]) :
    rightTransDeriv q (r • a) = r • rightTransDeriv q a := by
  simp only [← rightTransDerivCLM_apply, map_smul]
theorem exists_taylor_bound_apply (a : ℍ[ℝ]) : ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ ∀ q : ℍ[ℝ], ‖q‖ < r →
    ‖rightTransDeriv q a - a - fderiv ℝ (fun q => rightTransDeriv q a) 0 q‖ ≤ K * ‖q‖ ^ 2 := by
  set G : ℍ[ℝ] → ℍ[ℝ] := fun q => rightTransDeriv q a with hG
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ G) 0 := (contDiffAt_rightTransDeriv a).fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have h2 : ∀ᶠ q in nhds (0 : ℍ[ℝ]), ContDiffAt ℝ 2 G q := (contDiffAt_rightTransDeriv a).eventually (by simp)
  have ht' : ∀ᶠ q in nhds (0 : ℍ[ℝ]), q ∈ t := ht
  obtain ⟨r, hr, h3⟩ := Metric.eventually_nhds_iff.1 (ht'.and h2)
  refine ⟨(K : ℝ) + 1, r, by positivity, hr, fun q hq => ?_⟩
  have hin : ∀ x ∈ Metric.closedBall (0 : ℍ[ℝ]) ‖q‖, dist x 0 < r := fun x hx =>
    lt_of_le_of_lt (Metric.mem_closedBall.1 hx) (by simpa using hq)
  set D : ℍ[ℝ] →L[ℝ] ℍ[ℝ] := fderiv ℝ G 0 with hD
  have hder : ∀ x ∈ Metric.closedBall (0 : ℍ[ℝ]) ‖q‖,
      HasFDerivWithinAt (fun x => G x - D x) (fderiv ℝ G x - D) (Metric.closedBall 0 ‖q‖) x := by
    intro x hx
    have hd : DifferentiableAt ℝ G x := (h3 (hin x hx)).2.differentiableAt (by norm_num)
    exact (hd.hasFDerivAt.sub D.hasFDerivAt).hasFDerivWithinAt
  have hbound : ∀ x ∈ Metric.closedBall (0 : ℍ[ℝ]) ‖q‖, ‖fderiv ℝ G x - D‖ ≤ ((K : ℝ) + 1) * ‖q‖ := by
    intro x hx
    have hl := hK.dist_le_mul x (h3 (hin x hx)).1 0 (mem_of_mem_nhds ht)
    rw [dist_eq_norm, dist_zero_right] at hl
    have hx' : ‖x‖ ≤ ‖q‖ := by simpa using hx
    calc ‖fderiv ℝ G x - D‖ ≤ K * ‖x‖ := hl
      _ ≤ ((K : ℝ) + 1) * ‖q‖ := by
        have : (0 : ℝ) ≤ K := K.2
        nlinarith [norm_nonneg x, norm_nonneg q]
  have hmv := (convex_closedBall (0 : ℍ[ℝ]) ‖q‖).norm_image_sub_le_of_norm_hasFDerivWithin_le hder hbound
    (show (0 : ℍ[ℝ]) ∈ Metric.closedBall (0 : ℍ[ℝ]) ‖q‖ by simp)
    (show q ∈ Metric.closedBall (0 : ℍ[ℝ]) ‖q‖ by simp)
  simp only [map_zero, sub_zero, hG, rightTransDeriv_zero] at hmv
  have e : rightTransDeriv q a - a - fderiv ℝ (fun q => rightTransDeriv q a) 0 q = rightTransDeriv q a - D q - a := by
    rw [hD]
    abel
  rw [e, pow_two, ← mul_assoc]
  exact hmv
def basisQ : Fin 4 → ℍ[ℝ] := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨0, 0, 1, 0⟩, ⟨0, 0, 0, 1⟩]
def coordQ (a : ℍ[ℝ]) : Fin 4 → ℝ := ![a.re, a.imI, a.imJ, a.imK]
theorem eq_sum_coordQ (a : ℍ[ℝ]) : a = ∑ e, coordQ a e • basisQ e := by
  rw [Fin.sum_univ_four]
  ext
  · show a.re = coordQ a 0 * 1 + coordQ a 1 * 0 + coordQ a 2 * 0 + coordQ a 3 * 0
    simp [coordQ]
  · show a.imI = coordQ a 0 * 0 + coordQ a 1 * 1 + coordQ a 2 * 0 + coordQ a 3 * 0
    simp [coordQ]
  · show a.imJ = coordQ a 0 * 0 + coordQ a 1 * 0 + coordQ a 2 * 1 + coordQ a 3 * 0
    simp [coordQ]
  · show a.imK = coordQ a 0 * 0 + coordQ a 1 * 0 + coordQ a 2 * 0 + coordQ a 3 * 1
    simp [coordQ]
theorem abs_coordQ_le (a : ℍ[ℝ]) (e : Fin 4) : |coordQ a e| ≤ ‖a‖ := by
  have hsq : ‖a‖ ^ 2 = a.re ^ 2 + a.imI ^ 2 + a.imJ ^ 2 + a.imK ^ 2 := by
    rw [sq, ← Quaternion.normSq_eq_norm_mul_self, Quaternion.normSq_def']
  have hn := norm_nonneg a
  fin_cases e <;> simp only [coordQ] <;> refine abs_le_of_sq_le_sq ?_ hn <;> simp <;> nlinarith [sq_nonneg a.re, sq_nonneg a.imI, sq_nonneg a.imJ, sq_nonneg a.imK]
def linearPart (q a : ℍ[ℝ]) : ℍ[ℝ] := ∑ e, coordQ a e • fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q
theorem rightTransDeriv_eq_sum (q a : ℍ[ℝ]) : rightTransDeriv q a = ∑ e, coordQ a e • rightTransDeriv q (basisQ e) := by
  conv_lhs => rw [eq_sum_coordQ a]
  simp only [← rightTransDerivCLM_apply, map_sum, map_smul]
theorem linearPart_add_left (q q' a : ℍ[ℝ]) : linearPart (q + q') a = linearPart q a + linearPart q' a := by
  simp only [linearPart, map_add, smul_add, Finset.sum_add_distrib]
theorem linearPart_neg_left (q a : ℍ[ℝ]) : linearPart (-q) a = - linearPart q a := by
  simp only [linearPart, map_neg, smul_neg, Finset.sum_neg_distrib]
theorem coordQ_add (a b : ℍ[ℝ]) (e : Fin 4) : coordQ (a + b) e = coordQ a e + coordQ b e := by
  fin_cases e <;> simp [coordQ]
theorem linearPart_add_right (q a b : ℍ[ℝ]) : linearPart q (a + b) = linearPart q a + linearPart q b := by
  simp only [linearPart, coordQ_add, add_smul, Finset.sum_add_distrib]
theorem exists_norm_linearPart_le : ∃ K : ℝ, 0 < K ∧ ∀ q a : ℍ[ℝ], ‖linearPart q a‖ ≤ K * ‖q‖ * ‖a‖ := by
  refine ⟨1 + ∑ e, ‖fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0‖, by positivity, fun q a => ?_⟩
  have hterm : ∀ e, ‖coordQ a e • fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q‖ ≤
      ‖fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0‖ * ‖q‖ * ‖a‖ := by
    intro e
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := abs_coordQ_le a e
    have h2 := (fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0).le_opNorm q
    nlinarith [abs_nonneg (coordQ a e), norm_nonneg (fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q), norm_nonneg a,
      mul_nonneg (norm_nonneg (fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0)) (norm_nonneg q)]
  calc ‖linearPart q a‖ ≤ ∑ e, ‖coordQ a e • fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q‖ := norm_sum_le _ _
    _ ≤ ∑ e, ‖fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0‖ * ‖q‖ * ‖a‖ := Finset.sum_le_sum fun e _ => hterm e
    _ = (∑ e, ‖fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0‖) * ‖q‖ * ‖a‖ := by
      rw [Finset.sum_mul, Finset.sum_mul]
    _ ≤ _ := by
      have : 0 ≤ ‖q‖ * ‖a‖ := by positivity
      nlinarith
theorem exists_taylor_bound : ∃ K r : ℝ, 0 < K ∧ 0 < r ∧ ∀ q a : ℍ[ℝ], ‖q‖ < r →
    ‖rightTransDeriv q a - a - linearPart q a‖ ≤ K * ‖q‖ ^ 2 * ‖a‖ := by
  choose K r hK hr h using fun e => exists_taylor_bound_apply (basisQ e)
  refine ⟨∑ e, K e, Finset.univ.inf' ⟨0, Finset.mem_univ _⟩ r, Finset.sum_pos (fun e _ => hK e) ⟨0, Finset.mem_univ _⟩,
    (Finset.lt_inf'_iff _).2 fun e _ => hr e, fun q a hq => ?_⟩
  have hq' : ∀ e, ‖q‖ < r e := fun e => lt_of_lt_of_le hq (Finset.inf'_le _ (Finset.mem_univ e))
  have e1 : rightTransDeriv q a - a - linearPart q a = ∑ e, coordQ a e •
      (rightTransDeriv q (basisQ e) - basisQ e - fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q) := by
    have h1 := rightTransDeriv_eq_sum q a
    have h2 := eq_sum_coordQ a
    simp only [smul_sub, Finset.sum_sub_distrib]
    rw [← h1, ← h2]
    rfl
  rw [e1]
  have hterm : ∀ e, ‖coordQ a e • (rightTransDeriv q (basisQ e) - basisQ e - fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q)‖ ≤
      K e * ‖q‖ ^ 2 * ‖a‖ := by
    intro e
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := abs_coordQ_le a e
    have h2 := h e q (hq' e)
    calc |coordQ a e| * _ ≤ ‖a‖ * (K e * ‖q‖ ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _)
      _ = _ := by ring
  calc _ ≤ ∑ e, ‖coordQ a e • (rightTransDeriv q (basisQ e) - basisQ e - fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q)‖ :=
        norm_sum_le _ _
    _ ≤ ∑ e, K e * ‖q‖ ^ 2 * ‖a‖ := Finset.sum_le_sum fun e _ => hterm e
    _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
theorem hasDerivAt_rightTransDeriv_line (q a : ℍ[ℝ]) :
    HasDerivAt (fun t : ℝ => rightTransDeriv (t • q) a) (linearPart q a) 0 := by
  have line : ∀ e, HasDerivAt (fun t : ℝ => rightTransDeriv (t • q) (basisQ e))
      (fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q) 0 := by
    intro e
    have h1 : HasDerivAt (fun t : ℝ => t • q) q 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const q
    have hd : HasFDerivAt (fun q => rightTransDeriv q (basisQ e))
        (fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0) ((0 : ℝ) • q) := by
      rw [zero_smul]
      exact ((contDiffAt_rightTransDeriv _).differentiableAt (by norm_num)).hasFDerivAt
    exact hd.comp_hasDerivAt (0 : ℝ) h1
  have h2 : HasDerivAt (fun t : ℝ => ∑ e, coordQ a e • rightTransDeriv (t • q) (basisQ e))
      (∑ e, coordQ a e • fderiv ℝ (fun q => rightTransDeriv q (basisQ e)) 0 q) 0 :=
    HasDerivAt.fun_sum fun e _ => by
      have := (line e).const_smul (coordQ a e)
      exact this
  have e : (fun t : ℝ => rightTransDeriv (t • q) a) = fun t : ℝ => ∑ e, coordQ a e • rightTransDeriv (t • q) (basisQ e) := by
    funext t
    exact rightTransDeriv_eq_sum _ _
  rw [e]
  exact h2
def unitConjCLM (h : ℍ[ℝ]) : ℍ[ℝ] →L[ℝ] ℍ[ℝ] :=
  (ContinuousLinearMap.mul ℝ ℍ[ℝ] h).comp ((ContinuousLinearMap.mul ℝ ℍ[ℝ]).flip (star h))
theorem unitConjCLM_apply (h q : ℍ[ℝ]) : unitConjCLM h q = unitConj h q := by
  simp [unitConjCLM, unitConj, mul_assoc]
theorem unitConj_mul {h : ℍ[ℝ]} (hh : ‖h‖ = 1) (a b : ℍ[ℝ]) : unitConj h (a * b) = unitConj h a * unitConj h b := by
  simp only [unitConj]
  calc h * (a * b) * star h = h * a * 1 * b * star h := by simp [mul_assoc]
    _ = h * a * (star h * h) * b * star h := by rw [star_mul_self_of_norm_eq_one hh]
    _ = _ := by simp only [mul_assoc]
theorem differentiableAt_qlog {g : ℍ[ℝ]} (hg : ‖g - 1‖ < rightRadius) : DifferentiableAt ℝ qlog g :=
  (qlogRadii_spec.contDiffAt g hg).differentiableAt (by norm_num)
theorem fderiv_qlog_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) {g : ℍ[ℝ]} (hg : ‖g - 1‖ < rightRadius) (v : ℍ[ℝ]) :
    fderiv ℝ qlog (unitConj h g) (unitConj h v) = unitConj h (fderiv ℝ qlog g v) := by
  have hg' : ‖unitConj h g - 1‖ < rightRadius := by rw [norm_unitConj_sub_one hh]; exact hg
  have h1 : HasFDerivAt (fun x => qlog (unitConjCLM h x)) ((fderiv ℝ qlog (unitConj h g)).comp (unitConjCLM h)) g := by
    have d := (differentiableAt_qlog hg').hasFDerivAt
    rw [← unitConjCLM_apply] at d
    have := d.comp g (unitConjCLM h).hasFDerivAt
    rw [unitConjCLM_apply] at this
    exact this
  have h2 : HasFDerivAt (fun x => unitConjCLM h (qlog x)) ((unitConjCLM h).comp (fderiv ℝ qlog g)) g :=
    (unitConjCLM h).hasFDerivAt.comp g (differentiableAt_qlog hg).hasFDerivAt
  have hev : (fun x => qlog (unitConjCLM h x)) =ᶠ[nhds g] fun x => unitConjCLM h (qlog x) := by
    have : ∀ᶠ x in nhds g, ‖x - 1‖ < rightRadius := by
      have hc : ContinuousAt (fun x : ℍ[ℝ] => ‖x - 1‖) g := by fun_prop
      exact hc.eventually (gt_mem_nhds hg)
    filter_upwards [this] with x hx
    rw [unitConjCLM_apply, unitConjCLM_apply, qlog_unitConj hh hx]
  have := (h1.congr_of_eventuallyEq hev.symm).unique h2
  have e := congrArg (fun L : ℍ[ℝ] →L[ℝ] ℍ[ℝ] => L v) this
  simp only [ContinuousLinearMap.comp_apply, unitConjCLM_apply] at e
  exact e
theorem rightTransDeriv_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) {q : ℍ[ℝ]} (hq : ‖exp q - 1‖ < rightRadius) (a : ℍ[ℝ]) :
    rightTransDeriv (unitConj h q) (unitConj h a) = unitConj h (rightTransDeriv q a) := by
  unfold rightTransDeriv
  rw [exp_unitConj hh, ← unitConj_mul hh, fderiv_qlog_unitConj hh hq]
theorem linearPart_unitConj {h : ℍ[ℝ]} (hh : ‖h‖ = 1) (q a : ℍ[ℝ]) :
    linearPart (unitConj h q) (unitConj h a) = unitConj h (linearPart q a) := by
  have l1 := hasDerivAt_rightTransDeriv_line (unitConj h q) (unitConj h a)
  have l2 := (unitConjCLM h).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_rightTransDeriv_line q a)
  have hev : (fun t : ℝ => rightTransDeriv (t • unitConj h q) (unitConj h a)) =ᶠ[nhds 0]
      (unitConjCLM h) ∘ fun t : ℝ => rightTransDeriv (t • q) a := by
    have hcont : ContinuousAt (fun t : ℝ => ‖exp (t • q) - 1‖) 0 := by
      have : ContinuousAt (fun t : ℝ => exp (t • q)) 0 := by
        have c1 : ContinuousAt (exp : ℍ[ℝ] → ℍ[ℝ]) ((0 : ℝ) • q) := (exp_analytic (𝕂 := ℝ) _).continuousAt
        exact ContinuousAt.comp (f := fun t : ℝ => t • q) c1 (by fun_prop)
      fun_prop
    have hz : ‖exp ((0 : ℝ) • q) - 1‖ < rightRadius := by simpa using qlogRadii_spec.right_pos
    filter_upwards [hcont.eventually (gt_mem_nhds hz)] with t ht
    simp only [Function.comp, unitConjCLM_apply]
    have e : t • unitConj h q = unitConj h (t • q) := by simp [unitConj]
    rw [e, rightTransDeriv_unitConj hh ht]
  have l3 := l2.congr_of_eventuallyEq hev
  have := l1.unique l3
  rw [this, unitConjCLM_apply]
theorem exists_norm_exp_sub_one_lt : ∃ r : ℝ, 0 < r ∧ ∀ q : ℍ[ℝ], ‖q‖ < r →
    ‖exp q - 1‖ < rightRadius ∧ ‖exp (-q) - 1‖ < rightRadius := by
  obtain ⟨r, hr, h⟩ := Metric.eventually_nhds_iff.1 eventually_norm_exp_sub_one_lt
  refine ⟨r, hr, fun q hq => ⟨h (by simpa using hq), h (by simpa using hq)⟩⟩
theorem qlog_inv {g : ℍ[ℝ]} (hg : ‖g - 1‖ < rightRadius) : qlog g⁻¹ = - qlog g := by
  have h1 := qlogRadii_spec.qlog_exp (- qlog g) (by rw [norm_neg]; exact qlogRadii_spec.norm_qlog_lt g hg)
  rw [exp_neg, qlogRadii_spec.exp_qlog g hg] at h1
  exact h1
theorem fderiv_qlog_left_mul {w : ℍ[ℝ]} (h1 : ‖exp w - 1‖ < rightRadius) (h2 : ‖exp (-w) - 1‖ < rightRadius)
    (b : ℍ[ℝ]) : fderiv ℝ qlog (exp w) (exp w * b) = rightTransDeriv (-w) b := by
  have hc : HasDerivAt (fun τ : ℝ => exp (τ • b)) b 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) b (0 : ℝ)
  have hc' : HasDerivAt (fun τ : ℝ => exp (-(τ • b))) (-b) 0 := by
    have := hasDerivAt_exp_smul_const (𝕂 := ℝ) (-b) (0 : ℝ)
    simpa using this
  have c1 : HasDerivAt (fun τ : ℝ => exp w * exp (τ • b)) (exp w * b) 0 := hc.const_mul _
  have c2 : HasDerivAt (fun τ : ℝ => exp (-(τ • b)) * exp (-w)) (-b * exp (-w)) 0 := hc'.mul_const _
  have v1 : exp w * exp ((0 : ℝ) • b) = exp w := by simp
  have v2 : exp (-((0 : ℝ) • b)) * exp (-w) = exp (-w) := by simp
  have d1 : HasDerivAt (fun τ : ℝ => qlog (exp w * exp (τ • b))) (fderiv ℝ qlog (exp w) (exp w * b)) 0 := by
    have := (differentiableAt_qlog h1).hasFDerivAt
    rw [← v1] at this
    have r := this.comp_hasDerivAt (0 : ℝ) c1
    rw [v1] at r
    exact r
  have d2 : HasDerivAt (fun τ : ℝ => qlog (exp (-(τ • b)) * exp (-w)))
      (fderiv ℝ qlog (exp (-w)) (-b * exp (-w))) 0 := by
    have := (differentiableAt_qlog h2).hasFDerivAt
    rw [← v2] at this
    have r := this.comp_hasDerivAt (0 : ℝ) c2
    rw [v2] at r
    exact r
  have hev : (fun τ : ℝ => qlog (exp w * exp (τ • b))) =ᶠ[nhds 0]
      fun τ : ℝ => - qlog (exp (-(τ • b)) * exp (-w)) := by
    have hcont : ContinuousAt (fun τ : ℝ => ‖exp w * exp (τ • b) - 1‖) 0 := by
      have := c1.continuousAt
      fun_prop
    have hz : ‖exp w * exp ((0 : ℝ) • b) - 1‖ < rightRadius := by rw [v1]; exact h1
    filter_upwards [hcont.eventually (gt_mem_nhds hz)] with τ hτ
    have hi : (exp w * exp (τ • b))⁻¹ = exp (-(τ • b)) * exp (-w) := by
      rw [mul_inv_rev, exp_neg, exp_neg]
    rw [← hi, qlog_inv hτ, neg_neg]
  have d3 := (d2.neg).congr_of_eventuallyEq hev
  have := d1.unique d3
  rw [this]
  unfold rightTransDeriv
  rw [neg_mul, map_neg, neg_neg]
theorem re_qlog {g : ℍ[ℝ]} (hn : ‖g‖ = 1) (hg : ‖g - 1‖ < rightRadius) : (qlog g).re = 0 := by
  have h := qlogRadii_spec.exp_qlog g hg
  have h2 : ‖exp (qlog g)‖ = 1 := by rw [h, hn]
  rw [Quaternion.norm_exp, ← Real.exp_eq_exp_ℝ, Real.norm_of_nonneg (Real.exp_pos _).le] at h2
  exact Real.exp_eq_one_iff _ |>.1 h2
theorem norm_exp_of_re_eq_zero {w : ℍ[ℝ]} (hw : w.re = 0) : ‖exp w‖ = 1 := by
  rw [Quaternion.norm_exp, hw]
  simp
theorem re_rightTransDeriv {w a : ℍ[ℝ]} (hw : w.re = 0) (ha : a.re = 0) (h1 : ‖exp w - 1‖ < rightRadius) :
    (rightTransDeriv w a).re = 0 := by
  have hc : HasDerivAt (fun τ : ℝ => exp (τ • a)) a 0 := by
    simpa using hasDerivAt_exp_smul_const (𝕂 := ℝ) a (0 : ℝ)
  have c1 : HasDerivAt (fun τ : ℝ => exp (τ • a) * exp w) (a * exp w) 0 := hc.mul_const _
  have v1 : exp ((0 : ℝ) • a) * exp w = exp w := by simp
  have d1 : HasDerivAt (fun τ : ℝ => qlog (exp (τ • a) * exp w)) (rightTransDeriv w a) 0 := by
    have := (differentiableAt_qlog h1).hasFDerivAt
    rw [← v1] at this
    have r := this.comp_hasDerivAt (0 : ℝ) c1
    rw [v1] at r
    exact r
  have d2 : HasDerivAt (fun τ : ℝ => (qlog (exp (τ • a) * exp w)).re) (rightTransDeriv w a).re 0 :=
    (⟨QuaternionAlgebra.reₗ _ _ _, Quaternion.continuous_re⟩ : ℍ[ℝ] →L[ℝ] ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) d1
  have hcont : ContinuousAt (fun τ : ℝ => ‖exp (τ • a) * exp w - 1‖) 0 := by
    have := c1.continuousAt
    fun_prop
  have hz : ‖exp ((0 : ℝ) • a) * exp w - 1‖ < rightRadius := by rw [v1]; exact h1
  have hev : (fun τ : ℝ => (qlog (exp (τ • a) * exp w)).re) =ᶠ[nhds 0] fun _ => (0 : ℝ) := by
    filter_upwards [hcont.eventually (gt_mem_nhds hz)] with τ hτ
    have hn : ‖exp (τ • a) * exp w‖ = 1 := by
      rw [norm_mul, norm_exp_of_re_eq_zero hw, norm_exp_of_re_eq_zero (by simp [ha]), one_mul]
    exact re_qlog hn hτ
  exact d2.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
end QuaternionLog
end YangMills.Construction
end
