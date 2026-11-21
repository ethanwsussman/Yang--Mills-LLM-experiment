import YangMills.Construction.EuclideanAnalysis.ExponentialMomentsFromHolomorphyOfTheTransform
import YangMills.Construction.FreeKernel.LineIntegrationByPartsProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal Nat
namespace YangMills.Construction.EuclideanAnalysis.HolomorphicCharFun
variable {μ : Measure ℝ} [IsFiniteMeasure μ]
lemma tendsto_cos_secondDiffQuot (x : ℝ) {t : ℕ → ℝ} (ht_ne : ∀ n, t n ≠ 0)
    (ht_lim : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun n => 2 * (1 - Real.cos (t n * x)) / t n ^ 2) atTop (𝓝 (x ^ 2)) := by
  have hx : Tendsto (fun n => t n * x) atTop (𝓝 0) := by simpa using ht_lim.mul_const x
  have hb : Tendsto (fun n => 5 / 48 * t n ^ 2 * x ^ 4) atTop (𝓝 0) := by
    simpa using ((ht_lim.pow 2).const_mul (5 / 48 : ℝ)).mul_const (x ^ 4)
  have hev : ∀ᶠ n in atTop, |t n * x| < 1 :=
    (tendsto_order.1 (by simpa using hx.abs)).2 1 one_pos
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hb
  filter_upwards [hev] with n hn
  have hc := Real.cos_bound hn.le
  have htn := ht_ne n
  have hpos : 0 < t n ^ 2 := by positivity
  have e : 2 * (1 - Real.cos (t n * x)) / t n ^ 2 - x ^ 2 =
      -2 * (Real.cos (t n * x) - (1 - (t n * x) ^ 2 / 2)) / t n ^ 2 := by
    field_simp
    ring
  have h4 : |t n * x| ^ 4 = (t n * x) ^ 4 := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, sq_abs, ← pow_mul]
  rw [Real.norm_eq_abs, e, abs_div, abs_mul, abs_of_pos hpos, div_le_iff₀ hpos,
    show |(-2 : ℝ)| = 2 by norm_num]
  calc 2 * |Real.cos (t n * x) - (1 - (t n * x) ^ 2 / 2)|
      ≤ 2 * (|t n * x| ^ 4 * (5 / 96)) := by linarith
    _ = 5 / 48 * t n ^ 2 * x ^ 4 * t n ^ 2 := by rw [h4]; ring
lemma norm_cexp_I_mul_mul (s x : ℝ) : ‖Complex.exp (Complex.I * s * x)‖ = 1 := by apply _root_.YangMills.Construction.FreeKernel.LineIntegration.norm_character <;> assumption
lemma integrable_cexp_I_mul_mul {v : ℝ → ℂ} (hv : Integrable v μ) (s : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (Complex.I * s * x) * v x) μ := by
  refine hv.mono ?_ (Eventually.of_forall fun x => ?_)
  · exact (Continuous.aestronglyMeasurable (by fun_prop)).mul hv.aestronglyMeasurable
  · rw [norm_mul, norm_cexp_I_mul_mul, one_mul]
lemma exists_eq_add_mul_of_differentiableOn {r : ℝ} (hr : 0 < r) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r)) :
    ∃ g₁ : ℂ → ℂ, DifferentiableOn ℂ g₁ (Metric.ball 0 r) ∧ ∀ z, g z = g 0 + z * g₁ z := by
  refine ⟨dslope g 0, (Complex.differentiableOn_dslope (Metric.ball_mem_nhds 0 hr)).2 hg,
    fun z => ?_⟩
  have := sub_smul_dslope g 0 z
  simp only [sub_zero, smul_eq_mul] at this
  rw [this]
  ring
theorem integrable_sq_mul_of_charFun {r : ℝ} (hr : 0 < r) {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w μ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r))
    (hgw : ∀ s ∈ Ioo (-r) r,
      ∫ x : ℝ, Complex.exp (Complex.I * s * x) * (w x : ℂ) ∂μ = g s) :
    Integrable (fun x => x ^ 2 * w x) μ := by
  obtain ⟨g₁, hd₁, e₁⟩ := exists_eq_add_mul_of_differentiableOn hr hg
  obtain ⟨g₂, hd₂, e₂⟩ := exists_eq_add_mul_of_differentiableOn hr hd₁
  have hc₂ : ContinuousAt g₂ 0 :=
    (hd₂.differentiableAt (Metric.ball_mem_nhds 0 hr)).continuousAt
  have e₃ : ∀ z, 2 * g 0 - g z - g (-z) = -(z ^ 2 * (g₂ z + g₂ (-z))) := fun z => by
    rw [e₁ z, e₁ (-z), e₂ z, e₂ (-z)]
    ring
  have hwc : Integrable (fun x => (w x : ℂ)) μ := hwi.ofReal
  have hm : ∀ a : ℝ, Measurable fun x => 2 * (1 - Real.cos (a * x)) * w x := fun a => by
    fun_prop
  have hi : ∀ a : ℝ, Integrable (fun x => 2 * (1 - Real.cos (a * x)) * w x) μ := fun a => by
    refine (hwi.const_mul 4).mono (hm a).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have h1 := Real.neg_one_le_cos (a * x)
    have h2 := Real.cos_le_one (a * x)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) (hw0 x)),
      abs_of_nonneg (mul_nonneg (by norm_num) (hw0 x))]
    exact mul_le_mul_of_nonneg_right (by linarith) (hw0 x)
  have key : ∀ a : ℝ, a ∈ Ioo (-r) r →
      ((∫ x, 2 * (1 - Real.cos (a * x)) * w x ∂μ : ℝ) : ℂ) =
        2 * g 0 - g a - g (-(a : ℂ)) := by
    intro a ha
    have h0 := hgw 0 ⟨by linarith, hr⟩
    have hp := hgw a ha
    have hn := hgw (-a) ⟨by linarith [ha.2], by linarith [ha.1]⟩
    have hz : g 0 = g ((0 : ℝ) : ℂ) := by simp
    have hz' : g (-(a : ℂ)) = g ((-a : ℝ) : ℂ) := by simp
    have hE : ∀ t : ℝ, Integrable
        (fun x : ℝ => Complex.exp (Complex.I * t * x) * (w x : ℂ)) μ :=
      integrable_cexp_I_mul_mul hwc
    have i0 : Integrable
        (fun x : ℝ => 2 * (Complex.exp (Complex.I * (0 : ℝ) * x) * (w x : ℂ))) μ :=
      (hE 0).const_mul 2
    have i1 : Integrable (fun x : ℝ => 2 * (Complex.exp (Complex.I * (0 : ℝ) * x) * (w x : ℂ)) -
        Complex.exp (Complex.I * a * x) * (w x : ℂ)) μ := i0.sub (hE a)
    rw [hz, hz', ← h0, ← hp, ← hn, ← integral_const_mul, ← integral_sub i0 (hE a),
      ← integral_sub i1 (hE (-a)), ← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have hc := Complex.two_cos ((a * x : ℝ) : ℂ)
    have a1 : ((a * x : ℝ) : ℂ) * Complex.I = Complex.I * a * x := by push_cast; ring
    have a2 : -((a * x : ℝ) : ℂ) * Complex.I = Complex.I * ((-a : ℝ) : ℂ) * x := by
      push_cast; ring
    rw [a1, a2] at hc
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul]
    push_cast at hc ⊢
    linear_combination (-(w x : ℂ)) * hc
  obtain ⟨h, hne, h0, hmem⟩ : ∃ h : ℕ → ℝ, (∀ n, h n ≠ 0) ∧ Tendsto h atTop (𝓝 0) ∧
      ∀ n, h n ∈ Ioo (-r) r := by
    refine ⟨fun n => r / 2 * (1 / ((n : ℝ) + 1)), fun n => by positivity, ?_, fun n => ?_⟩
    · simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (r / 2)
    · have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
        rw [div_le_one hn]
        linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
      constructor <;> nlinarith
  have hF0 : ∀ n x, 0 ≤ 2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2 := fun n x => by
    have := Real.cos_le_one (h n * x)
    exact div_nonneg (mul_nonneg (by linarith) (hw0 x)) (by positivity)
  have hlim : ∀ x, Tendsto (fun n => ENNReal.ofReal (2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2))
      atTop (𝓝 (ENNReal.ofReal (x ^ 2 * w x))) := fun x => by
    refine ENNReal.tendsto_ofReal ?_
    refine ((tendsto_cos_secondDiffQuot x hne h0).mul_const (w x)).congr fun n => ?_
    ring
  have hfat : ∫⁻ x, ENNReal.ofReal (x ^ 2 * w x) ∂μ ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2) ∂μ)
        atTop := by
    calc ∫⁻ x, ENNReal.ofReal (x ^ 2 * w x) ∂μ
        = ∫⁻ x, liminf (fun n => ENNReal.ofReal (2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2))
            atTop ∂μ := lintegral_congr fun x => (hlim x).liminf_eq.symm
      _ ≤ _ := lintegral_liminf_le fun n => by fun_prop
  have hI : ∀ n, ∫⁻ x, ENNReal.ofReal (2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2) ∂μ =
      ENNReal.ofReal (∫ x, 2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2 ∂μ) := fun n =>
    (ofReal_integral_eq_lintegral_ofReal ((hi (h n)).div_const _)
      (Eventually.of_forall (hF0 n))).symm
  have hAc : ∀ n, ((∫ x, 2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2 ∂μ : ℝ) : ℂ) =
      -(g₂ (h n) + g₂ (-(h n : ℂ))) := fun n => by
    have hhn : (h n : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hne n)
    rw [integral_div, Complex.ofReal_div, key _ (hmem n), e₃]
    push_cast
    field_simp
  have hz : Tendsto (fun n => ((h n : ℝ) : ℂ)) atTop (𝓝 0) := by
    simpa [Function.comp_def] using (Complex.continuous_ofReal.tendsto 0).comp h0
  have hz' : Tendsto (fun n => -((h n : ℝ) : ℂ)) atTop (𝓝 0) := by simpa using hz.neg
  have hAlim : Tendsto (fun n => ∫ x, 2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2 ∂μ) atTop
      (𝓝 (-(g₂ 0 + g₂ 0)).re) := by
    have hc : Tendsto (fun n => ((∫ x, 2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2 ∂μ : ℝ) : ℂ))
        atTop (𝓝 (-(g₂ 0 + g₂ 0))) := by
      simp_rw [hAc]
      exact ((hc₂.tendsto.comp hz).add (hc₂.tendsto.comp hz')).neg
    simpa [Function.comp_def] using (Complex.continuous_re.tendsto _).comp hc
  have hL : Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (2 * (1 - Real.cos (h n * x)) * w x / h n ^ 2) ∂μ)
      atTop (𝓝 (ENNReal.ofReal (-(g₂ 0 + g₂ 0)).re)) := by
    simp_rw [hI]
    exact ENNReal.tendsto_ofReal hAlim
  rw [hL.liminf_eq] at hfat
  refine ⟨(by fun_prop : Measurable fun x => x ^ 2 * w x).aestronglyMeasurable, ?_⟩
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun x =>
    mul_nonneg (sq_nonneg x) (hw0 x))).2 (hfat.trans_lt ENNReal.ofReal_lt_top)
lemma hasDerivAt_weightedCharFun {v : ℝ → ℂ} (hv : Integrable v μ)
    (hxv : Integrable (fun x : ℝ => (x : ℂ) * v x) μ) (s : ℝ) :
    HasDerivAt (fun t : ℝ => ∫ x : ℝ, Complex.exp (Complex.I * t * x) * v x ∂μ)
      (∫ x : ℝ, Complex.exp (Complex.I * s * x) * (Complex.I * ((x : ℂ) * v x)) ∂μ) s := by
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (𝕜 := ℝ)
    (F := fun (t : ℝ) (x : ℝ) => Complex.exp (Complex.I * t * x) * v x)
    (F' := fun (t : ℝ) (x : ℝ) => Complex.exp (Complex.I * t * x) * (Complex.I * ((x : ℂ) * v x)))
    (x₀ := s) (s := univ) (bound := fun x => ‖(x : ℂ) * v x‖) univ_mem
    (Eventually.of_forall fun t => (integrable_cexp_I_mul_mul hv t).aestronglyMeasurable)
    (integrable_cexp_I_mul_mul hv s)
    (integrable_cexp_I_mul_mul (hxv.const_mul Complex.I) s).aestronglyMeasurable
    (Eventually.of_forall fun x t _ => ?_) hxv.norm
    (Eventually.of_forall fun x t _ => ?_)).2
  · rw [norm_mul, norm_cexp_I_mul_mul, one_mul, norm_mul, Complex.norm_I, one_mul]
  · have h1 : HasDerivAt (fun t : ℝ => Complex.I * (t : ℂ) * x) (Complex.I * x) t := by
      simpa using ((hasDerivAt_id t).ofReal_comp.const_mul Complex.I).mul_const (x : ℂ)
    exact show HasDerivAt (fun t : ℝ => Complex.exp (Complex.I * t * x) * v x)
        (Complex.exp (Complex.I * t * x) * (Complex.I * ((x : ℂ) * v x))) t from by
      rw [show Complex.exp (Complex.I * t * x) * (Complex.I * ((x : ℂ) * v x)) =
        Complex.exp (Complex.I * t * x) * (Complex.I * x) * v x by ring]
      exact h1.cexp.mul_const (v x)
lemma eq_deriv_of_eqOn_Ioo {r : ℝ} {G : ℂ → ℂ} (hG : DifferentiableOn ℂ G (Metric.ball 0 r))
    {F F' : ℝ → ℂ} (hF : ∀ t, HasDerivAt F (F' t) t)
    (hFG : ∀ t ∈ Ioo (-r) r, F t = G t) : ∀ t ∈ Ioo (-r) r, F' t = deriv G t := by
  intro t ht
  have hmem : Metric.ball (0 : ℂ) r ∈ 𝓝 (t : ℂ) := by
    refine Metric.isOpen_ball.mem_nhds ?_
    simpa [abs_lt] using ht
  have h1 : HasDerivAt (fun y : ℝ => G y) (deriv G t) t :=
    (hG.differentiableAt hmem).hasDerivAt.comp_ofReal
  have h2 : F =ᶠ[𝓝 t] fun y : ℝ => G y := by
    filter_upwards [Ioo_mem_nhds ht.1 ht.2] with y hy using hFG y hy
  exact (hF t).unique (h1.congr_of_eventuallyEq h2)
theorem sq_mul_integrable_and_charFun_eq {r : ℝ} (hr : 0 < r) {w : ℝ → ℝ} (hwm : Measurable w)
    (hw0 : ∀ x, 0 ≤ w x) (hwi : Integrable w μ) {g : ℂ → ℂ}
    (hg : DifferentiableOn ℂ g (Metric.ball 0 r))
    (hgw : ∀ s ∈ Ioo (-r) r,
      ∫ x : ℝ, Complex.exp (Complex.I * s * x) * (w x : ℂ) ∂μ = g s) :
    Integrable (fun x => x ^ 2 * w x) μ ∧ ∀ s ∈ Ioo (-r) r,
      ∫ x : ℝ, Complex.exp (Complex.I * s * x) * ((x ^ 2 * w x : ℝ) : ℂ) ∂μ =
        -deriv (deriv g) s := by
  have h2 := integrable_sq_mul_of_charFun hr hwm hw0 hwi hg hgw
  refine ⟨h2, fun s hs => ?_⟩
  have hv0 : Integrable (fun x => (w x : ℂ)) μ := hwi.ofReal
  have h1 : Integrable (fun x => x * w x) μ := by
    refine (hwi.add h2).mono (by fun_prop : Measurable fun x => x * w x).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    have hb : |x| ≤ 1 + x ^ 2 := by
      have := sq_abs x
      nlinarith [sq_nonneg (|x| - 1), abs_nonneg x]
    have hnn : 0 ≤ (w + fun x => x ^ 2 * w x) x := by
      simp only [Pi.add_apply]
      have := hw0 x
      positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, abs_mul, abs_of_nonneg (hw0 x)]
    simp only [Pi.add_apply]
    nlinarith [hw0 x]
  have hx1 : Integrable (fun x : ℝ => (x : ℂ) * (w x : ℂ)) μ := by
    simpa using h1.ofReal (𝕜 := ℂ)
  have hx2 : Integrable (fun x : ℝ => (x : ℂ) * (Complex.I * ((x : ℂ) * (w x : ℂ)))) μ := by
    have h2c : Integrable (fun x : ℝ => ((x ^ 2 * w x : ℝ) : ℂ)) μ := by
      simpa using h2.ofReal (𝕜 := ℂ)
    refine (h2c.const_mul Complex.I).congr (Eventually.of_forall fun x => ?_)
    simp only
    push_cast
    ring
  have s1 := eq_deriv_of_eqOn_Ioo hg (fun t => hasDerivAt_weightedCharFun hv0 hx1 t) hgw
  have s2 := eq_deriv_of_eqOn_Ioo (hg.deriv Metric.isOpen_ball)
    (fun t => hasDerivAt_weightedCharFun (hx1.const_mul Complex.I) hx2 t) s1 s hs
  rw [← s2, ← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  simp only
  push_cast
  linear_combination (Complex.exp (Complex.I * s * x) * (x : ℂ) ^ 2 * (w x : ℂ)) * hI
lemma differentiableOn_ball_iteratedDeriv {r : ℝ} {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r)) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) (Metric.ball 0 r) := by
  induction n with
  | zero => simpa using hf
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact ih.deriv Metric.isOpen_ball
theorem even_moment_integrable_and_charFun_eq {r : ℝ} (hr : 0 < r) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (Metric.ball 0 r))
    (hT : ∀ s ∈ Ioo (-r) r, ∫ x : ℝ, Complex.exp (Complex.I * s * x) ∂μ = f s) (k : ℕ) :
    Integrable (fun x : ℝ => x ^ (2 * k)) μ ∧ ∀ s ∈ Ioo (-r) r,
      ∫ x : ℝ, Complex.exp (Complex.I * s * x) * ((x ^ (2 * k) : ℝ) : ℂ) ∂μ =
        (-1) ^ k * iteratedDeriv (2 * k) f s := by
  induction k with
  | zero =>
    refine ⟨by simp, fun s hs => ?_⟩
    simpa using hT s hs
  | succ k ih =>
    obtain ⟨hi, he⟩ := ih
    obtain ⟨h2, hs⟩ := sq_mul_integrable_and_charFun_eq hr (w := fun x => x ^ (2 * k)) (by fun_prop)
      (fun x => by rw [pow_mul]; positivity) hi
      (g := fun z => (-1) ^ k * iteratedDeriv (2 * k) f z)
      ((differentiableOn_ball_iteratedDeriv hf _).const_mul _) he
    have e : ∀ x : ℝ, x ^ 2 * x ^ (2 * k) = x ^ (2 * (k + 1)) := fun x => by ring
    simp only [e] at h2 hs
    refine ⟨h2, fun s hs' => ?_⟩
    have d : ∀ (c : ℂ) (G : ℂ → ℂ), deriv (fun z => c * G z) = fun z => c * deriv G z :=
      fun c G => funext fun z => deriv_const_mul_field c
    rw [hs s hs', d, d, show 2 * (k + 1) = 2 * k + 1 + 1 by ring, iteratedDeriv_succ,
      iteratedDeriv_succ, pow_succ]
    ring
theorem expMomentsOfHolomorphicCharFun : ExpMomentsOfHolomorphicCharFun := by
  intro μ _ r₀ f hr hf hT η hη0 hηr
  have hev := even_moment_integrable_and_charFun_eq (μ := μ) hr hf hT
  have hM : ∀ k : ℕ, ((∫ x : ℝ, x ^ (2 * k) ∂μ : ℝ) : ℂ) =
      (-1) ^ k * iteratedDeriv (2 * k) f 0 := fun k => by
    have := (hev k).2 0 ⟨by linarith, hr⟩
    simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul] at this
    rw [← this, integral_complex_ofReal]
  have hnI : ‖Complex.I * (η : ℂ)‖ = η := by
    simp [abs_of_nonneg hη0]
  have hmem₁ : Complex.I * (η : ℂ) ∈ Metric.ball (0 : ℂ) r₀ := by
    rw [mem_ball_zero_iff, hnI]
    exact hηr
  have hmem₂ : -(Complex.I * (η : ℂ)) ∈ Metric.ball (0 : ℂ) r₀ := by
    rw [mem_ball_zero_iff, norm_neg, hnI]
    exact hηr
  have hp := Complex.hasSum_taylorSeries_on_ball hf hmem₁
  have hm := Complex.hasSum_taylorSeries_on_ball hf hmem₂
  have hsum := (hp.add hm).mul_left (1 / 2 : ℂ)
  have hinj : Function.Injective fun k : ℕ => 2 * k := fun a b h => by simpa using h
  have heven := (hinj.hasSum_iff (fun n hn => by
    have hodd : Odd n := by
      rw [← Nat.not_even_iff_odd]
      rintro ⟨k, rfl⟩
      exact hn ⟨k, by simp [two_mul]⟩
    simp only [sub_zero, hodd.neg_pow, neg_smul, smul_neg, add_neg_cancel, mul_zero])).2 hsum
  obtain ⟨c, hc⟩ : ∃ c : ℕ → ℝ, ∀ k, c k =
      η ^ (2 * k) * (∫ x : ℝ, x ^ (2 * k) ∂μ) / ((2 * k)! : ℝ) := ⟨_, fun _ => rfl⟩
  have hterm : ∀ k : ℕ, ((c k : ℝ) : ℂ) = (1 / 2 : ℂ) *
      (((2 * k)! : ℂ)⁻¹ • (Complex.I * (η : ℂ) - 0) ^ (2 * k) • iteratedDeriv (2 * k) f 0 +
        ((2 * k)! : ℂ)⁻¹ • (-(Complex.I * (η : ℂ)) - 0) ^ (2 * k) •
          iteratedDeriv (2 * k) f 0) := fun k => by
    have hpw : (Complex.I * (η : ℂ)) ^ (2 * k) = (-1) ^ k * (η : ℂ) ^ (2 * k) := by
      rw [mul_pow, pow_mul, Complex.I_sq]
    simp only [sub_zero, Even.neg_pow (even_two_mul k), smul_eq_mul, hpw]
    rw [hc k]
    push_cast
    rw [hM k]
    ring
  have heven' : HasSum (fun k => ((c k : ℝ) : ℂ))
      ((1 / 2 : ℂ) * (f (Complex.I * η) + f (-(Complex.I * η)))) := by
    rw [show (fun k => ((c k : ℝ) : ℂ)) = _ from funext hterm]
    exact heven
  have hsm : Summable c := Complex.summable_ofReal.1 heven'.summable
  have hS : ((∑' k, c k : ℝ) : ℂ) =
      (1 / 2 : ℂ) * (f (Complex.I * η) + f (-(Complex.I * η))) :=
    (Complex.hasSum_ofReal.2 hsm.hasSum).unique heven'
  have hFnn : ∀ (k : ℕ) (x : ℝ), 0 ≤ (η * x) ^ (2 * k) / ((2 * k)! : ℝ) := fun k x => by
    rw [pow_mul]
    positivity
  have hFi : ∀ k : ℕ, Integrable (fun x : ℝ => (η * x) ^ (2 * k) / ((2 * k)! : ℝ)) μ :=
    fun k => by
      simp_rw [mul_pow]
      exact ((hev k).1.const_mul _).div_const _
  have hFc : ∀ k : ℕ, ∫ x : ℝ, (η * x) ^ (2 * k) / ((2 * k)! : ℝ) ∂μ = c k := fun k => by
    simp_rw [mul_pow]
    rw [integral_div, integral_const_mul, hc k]
  have hcn : ∀ k, 0 ≤ c k := fun k => by
    rw [← hFc k]
    exact integral_nonneg (hFnn k)
  have hFn : ∀ k : ℕ, ∫ x : ℝ, ‖(η * x) ^ (2 * k) / ((2 * k)! : ℝ)‖ ∂μ = c k := fun k => by
    simp_rw [Real.norm_of_nonneg (hFnn k _)]
    exact hFc k
  have hH := hasSum_integral_of_summable_integral_norm hFi (by simp_rw [hFn]; exact hsm)
  have hct : ∀ x : ℝ, ∑' k : ℕ, (η * x) ^ (2 * k) / ((2 * k)! : ℝ) = Real.cosh (η * x) :=
    fun x => (Real.hasSum_cosh _).tsum_eq
  simp_rw [hct, hFc] at hH
  have hcosh : ∫ x : ℝ, Real.cosh (η * x) ∂μ = ∑' k, c k := hH.tsum_eq.symm
  refine ⟨?_, by rw [hcosh, hS]⟩
  have hl : ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (η * x)) ∂μ = ENNReal.ofReal (∑' k, c k) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hcn hsm]
    calc ∫⁻ x : ℝ, ENNReal.ofReal (Real.cosh (η * x)) ∂μ
        = ∫⁻ x : ℝ, ∑' k : ℕ, ENNReal.ofReal ((η * x) ^ (2 * k) / ((2 * k)! : ℝ)) ∂μ :=
          lintegral_congr fun x => by
            rw [← hct x, ENNReal.ofReal_tsum_of_nonneg (fun k => hFnn k x)
              (Real.hasSum_cosh _).summable]
      _ = ∑' k : ℕ, ∫⁻ x : ℝ, ENNReal.ofReal ((η * x) ^ (2 * k) / ((2 * k)! : ℝ)) ∂μ :=
          lintegral_tsum fun k => by fun_prop
      _ = ∑' k, ENNReal.ofReal (c k) := by
          congr 1
          funext k
          rw [← ofReal_integral_eq_lintegral_ofReal (hFi k)
            (Eventually.of_forall (hFnn k)), hFc]
  have hb : ∀ x : ℝ, ENNReal.ofReal (Real.exp (η * |x|)) ≤
      2 * ENNReal.ofReal (Real.cosh (η * x)) := fun x => by
    have h1 : Real.exp (η * |x|) ≤ 2 * Real.cosh (η * x) := by
      have p1 := Real.exp_pos (η * x)
      have p2 := Real.exp_pos (-(η * x))
      rw [Real.cosh_eq]
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]
        linarith
      · rw [abs_of_nonpos h, mul_neg]
        linarith
    calc ENNReal.ofReal (Real.exp (η * |x|))
        ≤ ENNReal.ofReal (2 * Real.cosh (η * x)) := ENNReal.ofReal_le_ofReal h1
      _ = 2 * ENNReal.ofReal (Real.cosh (η * x)) := by
          rw [ENNReal.ofReal_mul (by norm_num)]
          simp
  calc ∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (η * |x|)) ∂μ
      ≤ ∫⁻ x : ℝ, 2 * ENNReal.ofReal (Real.cosh (η * x)) ∂μ := lintegral_mono hb
    _ = 2 * ENNReal.ofReal (∑' k, c k) := by
        rw [lintegral_const_mul _ (by fun_prop), hl]
    _ < ∞ := ENNReal.mul_lt_top (by simp) ENNReal.ofReal_lt_top
end YangMills.Construction.EuclideanAnalysis.HolomorphicCharFun
