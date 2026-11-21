import YangMills.Construction.JointSpectrum.DiscTwoConstants
import Mathlib
set_option autoImplicit false
open MeasureTheory Metric Filter Topology
open scoped ENNReal NNReal
noncomputable section
namespace YangMills.Construction.DiscTwoConstants
open YangMills.Construction.DiscGeometry
theorem exists_poly_sq_eq_evenPart (T : Polynomial ℂ) :
    ∃ P : Polynomial ℂ, ∀ y : ℂ, P.eval (y ^ 2) = (T.eval y + T.eval (-y)) / 2 := by
  induction T using Polynomial.induction_on' with
  | add p r hp hr =>
    obtain ⟨P, hP⟩ := hp
    obtain ⟨Q, hQ⟩ := hr
    refine ⟨P + Q, fun y => ?_⟩
    simp only [Polynomial.eval_add, hP, hQ]
    ring
  | monomial n a =>
    rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
    · refine ⟨Polynomial.monomial k a, fun y => ?_⟩
      simp only [Polynomial.eval_monomial]
      rw [pow_mul, pow_mul, neg_sq]
      ring
    · refine ⟨0, fun y => ?_⟩
      simp only [Polynomial.eval_monomial, Polynomial.eval_zero]
      rw [Odd.neg_pow ⟨k, rfl⟩]
      ring
theorem exists_poly_sq_approx_of_even {H : ℂ → ℂ} {R : ℝ} (hR : 1 < R)
    (hH : DifferentiableOn ℂ H (ball 0 R)) (heven : ∀ y ∈ ball (0 : ℂ) R, H (-y) = H y)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ P : Polynomial ℂ, ∀ y : ℂ, ‖y‖ ≤ 1 → ‖P.eval (y ^ 2) - H y‖ ≤ ε := by
  obtain ⟨r₁, h1, hr₁⟩ := exists_between hR
  obtain ⟨r₀, h0, hr₀⟩ := exists_between h1
  have hr₁pos : 0 < r₁ := by linarith
  have hr₀pos : 0 < r₀ := by linarith
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = r₁ := ⟨⟨r₁, hr₁pos.le⟩, rfl⟩
  obtain ⟨ρ₀, hρ₀⟩ : ∃ ρ : ℝ≥0, (ρ : ℝ) = r₀ := ⟨⟨r₀, hr₀pos.le⟩, rfl⟩
  have hd : DifferentiableOn ℂ H (closedBall 0 ρ₁) :=
    hH.mono (closedBall_subset_ball (by rw [hρ₁]; exact hr₁))
  have hρ₁pos : 0 < ρ₁ := by
    rw [← NNReal.coe_pos, hρ₁]
    exact hr₁pos
  have hρlt : ρ₀ < ρ₁ := by
    rw [← NNReal.coe_lt_coe, hρ₀, hρ₁]
    exact hr₀
  obtain ⟨p, hser⟩ : ∃ p, HasFPowerSeriesOnBall H p 0 (ρ₁ : ℝ≥0∞) :=
    ⟨_, hd.hasFPowerSeriesOnBall hρ₁pos⟩
  have hu := hser.tendstoUniformlyOn (r' := ρ₀) (ENNReal.coe_lt_coe.mpr hρlt)
  rw [Metric.tendstoUniformlyOn_iff] at hu
  obtain ⟨n, hn⟩ := (hu ε hε).exists
  let T : Polynomial ℂ := ∑ k ∈ Finset.range n, Polynomial.monomial k (p.coeff k)
  have hT : ∀ y : ℂ, T.eval y = p.partialSum n y := by
    intro y
    simp only [T, Polynomial.eval_finsetSum, Polynomial.eval_monomial,
      FormalMultilinearSeries.partialSum, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      smul_eq_mul]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  obtain ⟨P, hP⟩ := exists_poly_sq_eq_evenPart T
  refine ⟨P, fun y hy => ?_⟩
  have hyb : y ∈ ball (0 : ℂ) ρ₀ := by
    rw [hρ₀]
    simpa using lt_of_le_of_lt hy h0
  have hnb : -y ∈ ball (0 : ℂ) ρ₀ := by
    rw [hρ₀]
    simpa using lt_of_le_of_lt hy h0
  have hyR : y ∈ ball (0 : ℂ) R := by
    simpa using lt_of_le_of_lt hy (h0.trans (hr₀.trans hr₁))
  have e1 := hn y hyb
  have e2 := hn (-y) hnb
  simp only [zero_add, dist_eq_norm] at e1 e2
  rw [← hT] at e1 e2
  have hid : P.eval (y ^ 2) - H y
      = -((H y - T.eval y) + (H (-y) - T.eval (-y))) / 2 := by
    rw [hP, heven y hyR]
    ring
  rw [hid, norm_div, norm_neg]
  have htri := norm_add_le (H y - T.eval y) (H (-y) - T.eval (-y))
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h2, div_le_iff₀ (by norm_num)]
  linarith
def cayleyMap (w : ℂ) : ℂ := (1 + w) / (1 - w)
theorem one_sub_ne_zero_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) : 1 - w ≠ 0 := by
  intro h
  have : w = 1 := (sub_eq_zero.mp h).symm
  simp [this] at hw
theorem cayleyMap_re (w : ℂ) :
    (cayleyMap w).re = (1 - ‖w‖ ^ 2) / Complex.normSq (1 - w) := by
  rw [cayleyMap, Complex.div_re, Complex.sq_norm, Complex.normSq_apply w]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  ring
theorem cayleyMap_im (w : ℂ) :
    (cayleyMap w).im = 2 * w.im / Complex.normSq (1 - w) := by
  rw [cayleyMap, Complex.div_im]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  ring
theorem normSq_one_sub_pos_of_norm_lt_one {w : ℂ} (hw : ‖w‖ < 1) :
    0 < Complex.normSq (1 - w) :=
  Complex.normSq_pos.mpr (one_sub_ne_zero_of_norm_lt_one hw)
theorem cayleyMap_re_pos {w : ℂ} (hw : ‖w‖ < 1) : 0 < (cayleyMap w).re := by
  rw [cayleyMap_re]
  have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w]
  exact div_pos (by linarith) (normSq_one_sub_pos_of_norm_lt_one hw)
theorem abs_arg_cayleyMap_lt {w : ℂ} (hw : ‖w‖ < 1) : |(cayleyMap w).arg| < Real.pi / 2 :=
  Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (cayleyMap_re_pos hw))
theorem log_cayleyMap_neg {w : ℂ} (hw : ‖w‖ < 1) :
    Complex.log (cayleyMap (-w)) = -Complex.log (cayleyMap w) := by
  have h : cayleyMap (-w) = (cayleyMap w)⁻¹ := by
    simp only [cayleyMap, inv_div, sub_neg_eq_add, ← sub_eq_add_neg]
  rw [h, Complex.log_inv]
  intro harg
  have := abs_arg_cayleyMap_lt hw
  rw [harg, abs_of_pos Real.pi_pos] at this
  linarith [Real.pi_pos]
theorem norm_ccos_sq (x : ℂ) :
    ‖Complex.cos x‖ ^ 2 = Real.cos x.re ^ 2 + Real.sinh x.im ^ 2 := by
  have hcos : Complex.cos x = ((Real.cos x.re * Real.cosh x.im : ℝ) : ℂ)
      - ((Real.sin x.re * Real.sinh x.im : ℝ) : ℂ) * Complex.I := by
    rw [Complex.cos_eq]
    push_cast
    ring
  have hgen : ∀ A B : ℝ, Complex.normSq ((A : ℂ) - (B : ℂ) * Complex.I) = A * A + B * B := by
    intro A B
    simp [Complex.normSq_apply]
  rw [hcos, Complex.sq_norm, hgen]
  have h1 := Real.sin_sq_add_cos_sq x.re
  have h2 := Real.cosh_sq x.im
  have : Real.cos x.re * Real.cosh x.im * (Real.cos x.re * Real.cosh x.im)
      + Real.sin x.re * Real.sinh x.im * (Real.sin x.re * Real.sinh x.im)
      = Real.cos x.re ^ 2 * Real.cosh x.im ^ 2 + Real.sin x.re ^ 2 * Real.sinh x.im ^ 2 := by ring
  rw [this, h2]
  have h3 : Real.sin x.re ^ 2 = 1 - Real.cos x.re ^ 2 := by linarith
  rw [h3]
  ring
def logCosKernel (s q : ℝ) (y : ℂ) : ℂ :=
  Complex.cos ((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * y)))
theorem im_mul_log_cayleyMap (s : ℝ) (w : ℂ) :
    ((s : ℂ) * Complex.log (cayleyMap w)).im = s * (cayleyMap w).arg := by
  simp [Complex.log_im]
theorem norm_ofReal_mul_lt_one {q : ℝ} (hq0 : 0 < q) {y : ℂ} (hy : ‖y‖ < 1 / q) :
    ‖(q : ℂ) * y‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  rw [lt_div_iff₀ hq0] at hy
  linarith
theorem norm_ofReal_mul_lt_one_of_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {y : ℂ}
    (hy : ‖y‖ ≤ 1) : ‖(q : ℂ) * y‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le]
  nlinarith [norm_nonneg y]
theorem logCosKernel_differentiableOn {s q : ℝ} (hq0 : 0 < q) :
    DifferentiableOn ℂ (logCosKernel s q) (ball 0 (1 / q)) := by
  intro y hy
  have hy' : ‖y‖ < 1 / q := by simpa using hy
  have hw := norm_ofReal_mul_lt_one hq0 hy'
  have hdiv : DifferentiableAt ℂ (fun y : ℂ => cayleyMap ((q : ℂ) * y)) y := by
    unfold cayleyMap
    refine DifferentiableAt.div (by fun_prop) (by fun_prop) (one_sub_ne_zero_of_norm_lt_one hw)
  have hslit : cayleyMap ((q : ℂ) * y) ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (cayleyMap_re_pos hw))
  have hlog := hdiv.clog hslit
  exact ((hlog.const_mul (s : ℂ)).ccos).differentiableWithinAt
theorem logCosKernel_neg {s q : ℝ} (hq0 : 0 < q) {y : ℂ} (hy : y ∈ ball (0 : ℂ) (1 / q)) :
    logCosKernel s q (-y) = logCosKernel s q y := by
  have hy' : ‖y‖ < 1 / q := by simpa using hy
  have hw := norm_ofReal_mul_lt_one hq0 hy'
  simp only [logCosKernel, mul_neg]
  rw [log_cayleyMap_neg hw, mul_neg, Complex.cos_neg]
theorem norm_logCosKernel_le_cosh {s q : ℝ} (hs : 0 < s) (hq0 : 0 < q) (hq1 : q < 1) {y : ℂ}
    (hy : ‖y‖ ≤ 1) : ‖logCosKernel s q y‖ ≤ Real.cosh (Real.pi * s / 2) := by
  have hw := norm_ofReal_mul_lt_one_of_le hq0 hq1 hy
  have harg := abs_arg_cayleyMap_lt hw
  have hsq := norm_ccos_sq ((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * y)))
  rw [im_mul_log_cayleyMap] at hsq
  set v := s * (cayleyMap ((q : ℂ) * y)).arg with hv
  have hvabs : |v| ≤ |Real.pi * s / 2| := by
    have hpos : 0 < Real.pi * s / 2 := by positivity
    have hmul := mul_le_mul_of_nonneg_left harg.le hs.le
    rw [hv, abs_mul, abs_of_pos hs, abs_of_pos hpos]
    linarith
  have hcosh : Real.cosh v ≤ Real.cosh (Real.pi * s / 2) := Real.cosh_le_cosh.mpr hvabs
  have h1 : ‖logCosKernel s q y‖ ^ 2 ≤ Real.cosh v ^ 2 := by
    rw [logCosKernel, hsq, Real.cosh_sq]
    nlinarith [Real.cos_sq_le_one (((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * y))).re)]
  have h2 : ‖logCosKernel s q y‖ ≤ Real.cosh v :=
    le_of_sq_le_sq h1 (Real.cosh_pos v).le
  exact h2.trans hcosh
theorem norm_logCosKernel_ofReal_le_one {s q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : ‖logCosKernel s q (r : ℂ)‖ ≤ 1 := by
  have hy : ‖(r : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hr0]
    exact hr1
  have hw := norm_ofReal_mul_lt_one_of_le hq0 hq1 hy
  have hsq := norm_ccos_sq ((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * (r : ℂ))))
  rw [im_mul_log_cayleyMap] at hsq
  have him : (cayleyMap ((q : ℂ) * (r : ℂ))).im = 0 := by
    rw [cayleyMap_im]
    simp
  have harg : (cayleyMap ((q : ℂ) * (r : ℂ))).arg = 0 :=
    Complex.arg_eq_zero_iff.mpr ⟨(cayleyMap_re_pos hw).le, him⟩
  rw [harg, mul_zero, Real.sinh_zero] at hsq
  have h1 : ‖logCosKernel s q (r : ℂ)‖ ^ 2 ≤ 1 ^ 2 := by
    rw [logCosKernel, hsq]
    nlinarith [Real.cos_sq_le_one (((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * (r : ℂ)))).re)]
  exact le_of_sq_le_sq h1 zero_le_one
theorem sinh_le_norm_logCosKernel {s q : ℝ} (hs : 0 < s) (y : ℂ) :
    Real.sinh (s * |(cayleyMap ((q : ℂ) * y)).arg|) ≤ ‖logCosKernel s q y‖ := by
  have hsq := norm_ccos_sq ((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * y)))
  rw [im_mul_log_cayleyMap] at hsq
  have hval : Real.sinh (s * |(cayleyMap ((q : ℂ) * y)).arg|)
      = |Real.sinh (s * (cayleyMap ((q : ℂ) * y)).arg)| := by
    rw [Real.abs_sinh, abs_mul, abs_of_pos hs]
  rw [hval]
  refine abs_le_of_sq_le_sq ?_ (norm_nonneg _)
  rw [logCosKernel, hsq]
  nlinarith [sq_nonneg (Real.cos ((s : ℂ) * Complex.log (cayleyMap ((q : ℂ) * y))).re)]
def argLevelSet (q δ : ℝ) : Set closedUnitDisc :=
  {z | ∃ y : ℂ, y ^ 2 = (z : ℂ) ∧ Real.pi / 4 + δ ≤ |(cayleyMap ((q : ℂ) * y)).arg|}
theorem norm_le_one_of_sq_eq {y z : ℂ} (h : y ^ 2 = z) (hz : ‖z‖ ≤ 1) : ‖y‖ ≤ 1 := by
  rw [← h, norm_pow] at hz
  by_contra hc
  rw [not_le] at hc
  nlinarith [norm_nonneg y]
theorem chebyshev_bound_aux {C₀ s δ : ℝ} (hC₀ : 0 ≤ C₀) (hs : 0 < s)
    (hy : 2 ≤ s * (Real.pi / 4 + δ)) :
    0 < Real.sinh (s * (Real.pi / 4 + δ)) - 1 ∧
      C₀ * 2 * (Real.cosh (Real.pi * s / 2) + 1) ≤
        64 * C₀ * Real.exp (-2 * s * δ) * (Real.sinh (s * (Real.pi / 4 + δ)) - 1) ^ 2 := by
  set y := s * (Real.pi / 4 + δ) with hydef
  have hE : 6 ≤ Real.exp y := by
    have h1 : Real.exp 2 ≤ Real.exp y := Real.exp_le_exp.mpr hy
    have h2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]
      norm_num
    have h3 := Real.exp_one_gt_d9
    nlinarith
  have hinv : Real.exp (-y) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hD : Real.exp y / 4 ≤ Real.sinh y - 1 := by
    rw [Real.sinh_eq]
    linarith
  have hDpos : 0 < Real.sinh y - 1 := by linarith
  refine ⟨hDpos, ?_⟩
  set x := Real.pi * s / 2 with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hc : Real.cosh x + 1 ≤ 2 * Real.exp x := by
    rw [Real.cosh_eq]
    have h1 : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have h2 : 1 ≤ Real.exp x := Real.one_le_exp hx0
    linarith
  have hsq : (Real.exp y / 4) ^ 2 ≤ (Real.sinh y - 1) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hD 2
  have hexp : Real.exp (-2 * s * δ) * Real.exp y ^ 2 = Real.exp x := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    rw [hydef, hxdef]
    ring
  have hK : 0 ≤ 64 * C₀ * Real.exp (-2 * s * δ) := by positivity
  calc C₀ * 2 * (Real.cosh x + 1) ≤ C₀ * 2 * (2 * Real.exp x) := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
    _ = 64 * C₀ * Real.exp (-2 * s * δ) * (Real.exp y / 4) ^ 2 := by
        rw [← hexp]
        ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hK
theorem measure_argLevelSet_le (m : Measure closedUnitDisc) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : ∀ p : Polynomial ℂ, SqIntegralLeSupProduct m C₀ p) {q δ s : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hs : 0 < s) (hy : 2 ≤ s * (Real.pi / 4 + δ)) :
    m (argLevelSet q δ) ≤ ENNReal.ofReal (64 * C₀ * Real.exp (-2 * s * δ)) := by
  have hR : 1 < 1 / q := by
    rw [lt_div_iff₀ hq0]
    linarith
  obtain ⟨P, hP⟩ := exists_poly_sq_approx_of_even hR
    (logCosKernel_differentiableOn (s := s) hq0) (fun y hy => logCosKernel_neg hq0 hy) one_pos
  have hnear : ∀ y : ℂ, ‖y‖ ≤ 1 → ‖P.eval (y ^ 2)‖ ≤ ‖logCosKernel s q y‖ + 1 := by
    intro y hy
    have h1 := hP y hy
    have h2 := norm_sub_norm_le (P.eval (y ^ 2)) (logCosKernel s q y)
    linarith
  have hnear' : ∀ y : ℂ, ‖y‖ ≤ 1 → ‖logCosKernel s q y‖ - 1 ≤ ‖P.eval (y ^ 2)‖ := by
    intro y hy
    have h1 := hP y hy
    have h2 := norm_sub_norm_le (logCosKernel s q y) (P.eval (y ^ 2))
    rw [norm_sub_rev] at h2
    linarith
  have hsup1 : YangMills.Construction.LatticeBasics.supNormE
      (fun t : unitInterval => Polynomial.eval ((t : ℝ) : ℂ) P) ≤ ENNReal.ofReal 2 := by
    unfold YangMills.Construction.LatticeBasics.supNormE
    refine iSup_le fun t => ?_
    have ht0 : (0 : ℝ) ≤ t := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have hr0 : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
    have hr1 : Real.sqrt t ≤ 1 := Real.sqrt_le_one.mpr ht1
    have hrsq : ((Real.sqrt t : ℝ) : ℂ) ^ 2 = ((t : ℝ) : ℂ) := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt ht0]
    have hn : ‖((Real.sqrt t : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg hr0]
      exact hr1
    have h1 := hnear _ hn
    rw [hrsq] at h1
    have h2 := norm_logCosKernel_ofReal_le_one (s := s) hq0 hq1 hr0 hr1
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hsup2 : YangMills.Construction.LatticeBasics.supNormE
      (fun ζ : Circle => Polynomial.eval (ζ : ℂ) P) ≤
        ENNReal.ofReal (Real.cosh (Real.pi * s / 2) + 1) := by
    unfold YangMills.Construction.LatticeBasics.supNormE
    refine iSup_le fun ζ => ?_
    obtain ⟨y, hy2⟩ := IsAlgClosed.exists_pow_nat_eq (ζ : ℂ) (n := 2) two_pos
    have hn : ‖y‖ ≤ 1 := norm_le_one_of_sq_eq hy2 (Circle.norm_coe ζ).le
    have h1 := hnear y hn
    rw [hy2] at h1
    have h2 := norm_logCosKernel_le_cosh hs hq0 hq1 hn
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  obtain ⟨hDpos, hnum⟩ := chebyshev_bound_aux (δ := δ) hC₀ hs hy
  set D := Real.sinh (s * (Real.pi / 4 + δ)) - 1 with hD
  set K := 64 * C₀ * Real.exp (-2 * s * δ) with hKdef
  have hK : 0 ≤ K := by positivity
  have hsub : argLevelSet q δ ⊆
      {z : closedUnitDisc | ENNReal.ofReal (D ^ 2) ≤ ‖P.eval (z : ℂ)‖ₑ ^ 2} := by
    rintro z ⟨y, hy2, harg⟩
    have hn : ‖y‖ ≤ 1 := norm_le_one_of_sq_eq hy2 z.2
    have h1 := sinh_le_norm_logCosKernel (q := q) hs y
    have h2 : Real.sinh (s * (Real.pi / 4 + δ)) ≤
        Real.sinh (s * |(cayleyMap ((q : ℂ) * y)).arg|) :=
      Real.sinh_le_sinh.mpr (mul_le_mul_of_nonneg_left harg hs.le)
    have h3 := hnear' y hn
    rw [hy2] at h3
    have h4 : D ≤ ‖P.eval (z : ℂ)‖ := by linarith
    show ENNReal.ofReal (D ^ 2) ≤ ‖P.eval (z : ℂ)‖ₑ ^ 2
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hDpos.le h4 2)
  have hmeas : Measurable (fun z : closedUnitDisc => ‖P.eval (z : ℂ)‖ₑ ^ 2) :=
    ((P.continuous.comp continuous_subtype_val).enorm).measurable.pow_const 2
  have hmk := mul_meas_ge_le_lintegral (μ := m) hmeas (ENNReal.ofReal (D ^ 2))
  have hb := h P
  unfold SqIntegralLeSupProduct at hb
  have hupper : ∫⁻ z, ‖Polynomial.eval (z : ℂ) P‖ₑ ^ 2 ∂m ≤
      ENNReal.ofReal (C₀ * 2 * (Real.cosh (Real.pi * s / 2) + 1)) := by
    refine hb.trans ?_
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC₀]
    exact mul_le_mul' (mul_le_mul' le_rfl hsup1) hsup2
  have hc0 : ENNReal.ofReal (D ^ 2) ≠ 0 := (ENNReal.ofReal_pos.mpr (pow_pos hDpos 2)).ne'
  have hfinal : ENNReal.ofReal (D ^ 2) * m (argLevelSet q δ) ≤
      ENNReal.ofReal (D ^ 2) * ENNReal.ofReal K := by
    calc ENNReal.ofReal (D ^ 2) * m (argLevelSet q δ)
        ≤ ENNReal.ofReal (D ^ 2) *
            m {z : closedUnitDisc | ENNReal.ofReal (D ^ 2) ≤ ‖P.eval (z : ℂ)‖ₑ ^ 2} :=
          mul_le_mul' le_rfl (measure_mono hsub)
      _ ≤ _ := hmk
      _ ≤ _ := hupper
      _ ≤ ENNReal.ofReal (K * D ^ 2) := ENNReal.ofReal_le_ofReal hnum
      _ = _ := by
          rw [ENNReal.ofReal_mul hK, mul_comm]
  have hcancel := ENNReal.mul_le_mul_iff_right hc0 ENNReal.ofReal_ne_top |>.mp hfinal
  exact hcancel
theorem measure_argLevelSet_eq_zero (m : Measure closedUnitDisc) {C₀ : ℝ} (hC₀ : 0 ≤ C₀)
    (h : ∀ p : Polynomial ℂ, SqIntegralLeSupProduct m C₀ p) {q δ : ℝ} (hq0 : 0 < q)
    (hq1 : q < 1) (hδ : 0 < δ) : m (argLevelSet q δ) = 0 := by
  have ht : Tendsto (fun s : ℝ => ENNReal.ofReal (64 * C₀ * Real.exp (-2 * s * δ)))
      atTop (𝓝 0) := by
    have h1 : Tendsto (fun s : ℝ => (-(2 * δ)) * s) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    have h2 := Real.tendsto_exp_atBot.comp h1
    have h3 := h2.const_mul (64 * C₀)
    have h4 := (ENNReal.continuous_ofReal.tendsto _).comp h3
    rw [mul_zero, ENNReal.ofReal_zero] at h4
    refine h4.congr fun s => ?_
    simp only [Function.comp]
    congr 3
    ring
  have ha : 0 < Real.pi / 4 + δ := by
    have := Real.pi_pos
    positivity
  refine le_antisymm (ge_of_tendsto ht ?_) zero_le
  filter_upwards [eventually_ge_atTop (2 / (Real.pi / 4 + δ) + 1)] with s hs
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hsa : 2 ≤ s * (Real.pi / 4 + δ) := by
    have h1 : 2 / (Real.pi / 4 + δ) * (Real.pi / 4 + δ) = 2 := div_mul_cancel₀ _ ha.ne'
    nlinarith
  exact measure_argLevelSet_le m hC₀ h hq0 hq1 hs0 hsa
theorem pi_div_four_lt_abs_arg_of_re_lt {x : ℂ} (hre : 0 < x.re) (him : x.re < |x.im|) :
    Real.pi / 4 < |x.arg| := by
  by_contra hc
  rw [not_lt] at hc
  obtain ⟨h1, h2⟩ := abs_le.mp hc
  have hpi := Real.pi_pos
  have hmono := Real.strictMonoOn_tan.monotoneOn
  have harg : x.arg ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := ⟨by linarith, by linarith⟩
  have hu : Real.tan x.arg ≤ 1 := by
    have := hmono harg (⟨by linarith, by linarith⟩ : Real.pi / 4 ∈ Set.Ioo _ _) h2
    rwa [Real.tan_pi_div_four] at this
  have hl : -1 ≤ Real.tan x.arg := by
    have := hmono (⟨by linarith, by linarith⟩ : -(Real.pi / 4) ∈ Set.Ioo _ _) harg h1
    rwa [Real.tan_neg, Real.tan_pi_div_four] at this
  rw [Complex.tan_arg] at hu hl
  rw [div_le_one hre] at hu
  rw [le_div_iff₀ hre] at hl
  have : |x.im| ≤ x.re := abs_le.mpr ⟨by linarith, hu⟩
  linarith
def radiusSeq (n : ℕ) : ℝ := 1 - 1 / (((n + 1 : ℕ) : ℝ) + 1)
theorem radiusSeq_pos (n : ℕ) : 0 < radiusSeq n := by
  have h : (1 : ℝ) < ((n + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have := (div_lt_one (by linarith)).mpr h
  simp only [radiusSeq]
  linarith
theorem radiusSeq_lt_one (n : ℕ) : radiusSeq n < 1 := by
  have : 0 < 1 / (((n + 1 : ℕ) : ℝ) + 1) := by positivity
  simp only [radiusSeq]
  linarith
theorem tendsto_radiusSeq : Tendsto radiusSeq atTop (𝓝 1) := by
  have h := (tendsto_add_atTop_iff_nat 1).2
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h2 := h.const_sub 1
  rw [sub_zero] at h2
  exact h2
theorem exists_argLevelSet_of_mem_nearRegion (z : closedUnitDisc)
    (hz : (z : ℂ) ∈ nearRegion) :
    ∃ n k : ℕ, z ∈ argLevelSet (radiusSeq n) (1 / ((k : ℝ) + 1)) := by
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (z : ℂ) (n := 2) two_pos
  have hyn : ‖y‖ ≤ 1 := norm_le_one_of_sq_eq hy z.2
  have hnorm : ‖(z : ℂ)‖ = ‖y‖ ^ 2 := by
    rw [← hy, norm_pow]
  have e1 : ‖y‖ ^ 2 = y.re * y.re + y.im * y.im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have e2 : ‖1 + (z : ℂ)‖ ^ 2 =
      (1 + y.re * y.re - y.im * y.im) ^ 2 + (2 * y.re * y.im) ^ 2 := by
    rw [← hy, Complex.sq_norm, Complex.normSq_apply]
    simp only [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.one_re, Complex.one_im]
    ring
  have hN := hz.2
  rw [e2, hnorm, e1] at hN
  have hkey : (1 - ‖y‖ ^ 2) ^ 2 < 4 * y.im ^ 2 := by
    have : (1 - (y.re * y.re + y.im * y.im)) ^ 2 - 4 * y.im ^ 2 =
        (1 + y.re * y.re - y.im * y.im) ^ 2 + (2 * y.re * y.im) ^ 2
          - 4 * (y.re * y.re + y.im * y.im) := by ring
    rw [e1]
    linarith
  have hb : 1 - ‖y‖ ^ 2 < 2 * |y.im| := by
    have h2 : (1 - ‖y‖ ^ 2) ^ 2 < (2 * |y.im|) ^ 2 := by
      rw [mul_pow, sq_abs]
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h2
  have hg : Tendsto (fun n => 2 * radiusSeq n * |y.im| - (1 - radiusSeq n ^ 2 * ‖y‖ ^ 2)) atTop
      (𝓝 (2 * 1 * |y.im| - (1 - 1 ^ 2 * ‖y‖ ^ 2))) :=
    ((tendsto_radiusSeq.const_mul 2).mul_const _).sub
      (tendsto_const_nhds.sub ((tendsto_radiusSeq.pow 2).mul_const _))
  have hpos : 0 < 2 * 1 * |y.im| - (1 - 1 ^ 2 * ‖y‖ ^ 2) := by linarith
  obtain ⟨n, hn⟩ := (hg.eventually (lt_mem_nhds hpos)).exists
  have hq0 := radiusSeq_pos n
  have hq1 := radiusSeq_lt_one n
  have hw := norm_ofReal_mul_lt_one_of_le hq0 hq1 hyn
  have hwn : ‖(radiusSeq n : ℂ) * y‖ ^ 2 = radiusSeq n ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hq0.le, mul_pow]
  have hwi : ((radiusSeq n : ℂ) * y).im = radiusSeq n * y.im := by simp
  have hNs := normSq_one_sub_pos_of_norm_lt_one hw
  have him : (cayleyMap ((radiusSeq n : ℂ) * y)).re
      < |(cayleyMap ((radiusSeq n : ℂ) * y)).im| := by
    rw [cayleyMap_re, cayleyMap_im, abs_div, abs_of_pos hNs, hwn, hwi, abs_mul, abs_mul,
      abs_of_pos hq0, abs_of_pos (two_pos : (0 : ℝ) < 2)]
    refine div_lt_div_of_pos_right ?_ hNs
    nlinarith
  have harg := pi_div_four_lt_abs_arg_of_re_lt (cayleyMap_re_pos hw) him
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt (sub_pos.mpr harg)
  exact ⟨n, k, y, hy, by linarith⟩
theorem discTwoConstantsStatement_holds : DiscTwoConstantsStatement := by
  rintro m _ ⟨C₀, hC₀, h⟩
  have hsub : (Subtype.val ⁻¹' nearRegion : Set closedUnitDisc) ⊆
      ⋃ n : ℕ, ⋃ k : ℕ, argLevelSet (radiusSeq n) (1 / ((k : ℝ) + 1)) := by
    intro z hz
    obtain ⟨n, k, hnk⟩ := exists_argLevelSet_of_mem_nearRegion z hz
    exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨k, hnk⟩⟩
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun n => measure_iUnion_null fun k => ?_
  exact measure_argLevelSet_eq_zero m hC₀ h (radiusSeq_pos n) (radiusSeq_lt_one n) (by positivity)
end YangMills.Construction.DiscTwoConstants
