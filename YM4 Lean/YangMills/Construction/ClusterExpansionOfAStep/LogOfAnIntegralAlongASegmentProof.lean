import YangMills.Construction.ClusterExpansionOfAStep.CalculusOfASplit
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
namespace YangMills.Construction.Interpolation
section
variable {α : Type} [MeasurableSpace α] {μ : Measure α} {w f g : α → ℝ} {M : ℝ}
private lemma aestronglyMeasurable_tiltedTerm (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (τ : ℝ) :
    AEStronglyMeasurable (fun a => w a * Real.exp (f a + τ * g a)) μ := by
  refine hw.aestronglyMeasurable.mul ?_
  exact Real.continuous_exp.comp_aestronglyMeasurable (hf.add (hg.const_mul τ))
private lemma exp_tilt_le_of_abs_le (hf : ∀ᵐ a ∂μ, |f a| ≤ M) (hg : ∀ᵐ a ∂μ, |g a| ≤ M) (T : ℝ) (hT : 0 ≤ T) :
    ∀ᵐ a ∂μ, ∀ τ : ℝ, |τ| ≤ T → Real.exp (f a + τ * g a) ≤ Real.exp (M + T * M) := by
  filter_upwards [hf, hg] with a ha hb τ hτ
  apply Real.exp_le_exp.mpr
  have h1 : f a ≤ M := (abs_le.mp ha).2
  have h2 : τ * g a ≤ T * M := by
    calc τ * g a ≤ |τ * g a| := le_abs_self _
      _ = |τ| * |g a| := abs_mul _ _
      _ ≤ T * M := mul_le_mul hτ hb (abs_nonneg _) hT
  linarith
private lemma integrable_mul_tiltedTerm (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M)
    {G : α → ℝ} (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK : ∀ᵐ a ∂μ, |G a| ≤ K) (τ : ℝ) :
    Integrable (fun a => G a * (w a * Real.exp (f a + τ * g a))) μ := by apply _root_.YangMills.Construction.ClusterExpansionOfAStep.integrable_mul_weight_exp <;> assumption
private lemma continuous_tiltedIntegral (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M)
    {G : α → ℝ} (hG : AEStronglyMeasurable G μ) {K : ℝ} (hK : ∀ᵐ a ∂μ, |G a| ≤ K) :
    Continuous fun τ : ℝ => ∫ a, G a * (w a * Real.exp (f a + τ * g a)) ∂μ := by
  rw [continuous_iff_continuousAt]
  intro τ₀
  have hb := exp_tilt_le_of_abs_le hfM hgM (|τ₀| + 1) (by positivity)
  refine continuousAt_of_dominated (bound := fun a => K * (|w a| * Real.exp (M + (|τ₀| + 1) * M)))
    (Eventually.of_forall fun τ => hG.mul (aestronglyMeasurable_tiltedTerm hw hf hg τ)) ?_
    ((hw.abs.mul_const _).const_mul _) ?_
  · have hnear : ∀ᶠ τ in 𝓝 τ₀, |τ| ≤ |τ₀| + 1 := by
      have : ∀ᶠ τ in 𝓝 τ₀, |τ - τ₀| < 1 := by
        have := Metric.ball_mem_nhds τ₀ (one_pos)
        filter_upwards [this] with τ hτ
        simpa [Real.dist_eq] using hτ
      filter_upwards [this] with τ hτ
      have : |τ| ≤ |τ₀| + |τ - τ₀| := by
        have := abs_add_le τ₀ (τ - τ₀)
        simpa using this
      linarith
    filter_upwards [hnear] with τ hτ
    filter_upwards [hb, hK] with a ha hk
    have h3 := ha τ hτ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : |w a| * Real.exp (f a + τ * g a) ≤ |w a| * Real.exp (M + (|τ₀| + 1) * M) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    exact mul_le_mul hk this (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) ((abs_nonneg _).trans hk)
  · refine Eventually.of_forall fun a => ?_
    fun_prop
private lemma hasDerivAt_tiltedIntegral (hw : Integrable w μ) (hf : AEStronglyMeasurable f μ)
    (hg : AEStronglyMeasurable g μ) (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M) (τ₀ : ℝ) :
    HasDerivAt (fun τ : ℝ => ∫ a, w a * Real.exp (f a + τ * g a) ∂μ)
      (∫ a, g a * (w a * Real.exp (f a + τ₀ * g a)) ∂μ) τ₀ := by
  have hb := exp_tilt_le_of_abs_le hfM hgM (|τ₀| + 1) (by positivity)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ)
    (F := fun (τ : ℝ) a => w a * Real.exp (f a + τ * g a))
    (F' := fun (τ : ℝ) a => g a * (w a * Real.exp (f a + τ * g a)))
    (x₀ := τ₀) (s := Metric.ball τ₀ 1)
    (bound := fun a => M * (|w a| * Real.exp (M + (|τ₀| + 1) * M)))
    (Metric.ball_mem_nhds τ₀ one_pos)
    (Eventually.of_forall fun τ => aestronglyMeasurable_tiltedTerm hw hf hg τ) ?_
    (hg.mul (aestronglyMeasurable_tiltedTerm hw hf hg τ₀)) ?_
    ((hw.abs.mul_const _).const_mul _) ?_
  · exact key.2
  · have := integrable_mul_tiltedTerm hw hf hg hfM hgM (G := fun _ => (1 : ℝ)) aestronglyMeasurable_const
      (K := 1) (by simp) τ₀
    simpa using this
  · filter_upwards [hb, hgM] with a ha hk τ hτ
    have hτ' : |τ| ≤ |τ₀| + 1 := by
      have h1 : |τ - τ₀| < 1 := by simpa [Real.dist_eq] using hτ
      have := abs_add_le τ₀ (τ - τ₀)
      have h2 : |τ| ≤ |τ₀| + |τ - τ₀| := by simpa using this
      linarith
    have h3 := ha τ hτ'
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    have : |w a| * Real.exp (f a + τ * g a) ≤ |w a| * Real.exp (M + (|τ₀| + 1) * M) :=
      mul_le_mul_of_nonneg_left h3 (abs_nonneg _)
    exact mul_le_mul hk this (mul_nonneg (abs_nonneg _) (Real.exp_pos _).le) ((abs_nonneg _).trans hk)
  · refine Eventually.of_forall fun a τ _ => ?_
    have h1 : HasDerivAt (fun τ : ℝ => f a + τ * g a) (g a) τ := by
      simpa using ((hasDerivAt_id τ).mul_const (g a)).const_add (f a)
    have h2 := (h1.exp).const_mul (w a)
    exact h2.congr_deriv (by ring)
private lemma tiltedIntegral_pos (hμ : μ ≠ 0) (hw : Integrable w μ) (hw0 : ∀ᵐ a ∂μ, 0 < w a)
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfM : ∀ᵐ a ∂μ, |f a| ≤ M) (hgM : ∀ᵐ a ∂μ, |g a| ≤ M) (τ : ℝ) :
    0 < ∫ a, w a * Real.exp (f a + τ * g a) ∂μ := by
  have hint := integrable_mul_tiltedTerm hw hf hg hfM hgM (G := fun _ => (1 : ℝ)) aestronglyMeasurable_const
    (K := 1) (by simp) τ
  simp only [one_mul] at hint
  have hpos : ∀ᵐ a ∂μ, 0 < w a * Real.exp (f a + τ * g a) := by
    filter_upwards [hw0] with a ha
    exact mul_pos ha (Real.exp_pos _)
  rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun a h => h.le) hint]
  have hsub : (Function.support fun a => w a * Real.exp (f a + τ * g a))ᶜ ⊆
      {a | ¬ 0 < w a * Real.exp (f a + τ * g a)} := by
    intro a ha h
    exact ha h.ne'
  have h0 : μ (Function.support fun a => w a * Real.exp (f a + τ * g a))ᶜ = 0 :=
    measure_mono_null hsub hpos
  by_contra hc
  have hc' : μ (Function.support fun a => w a * Real.exp (f a + τ * g a)) = 0 := by
    simpa using hc
  apply hμ
  have : μ Set.univ = 0 := by
    have := measure_union_null hc' h0
    simpa using this
  exact Measure.measure_univ_eq_zero.mp this
end
theorem logIntegralExpInterpolation : LogIntegralExpInterpolationStatement := by
  intro α _ μ w f g M hμ hw hw0 hf hg hfM hgM
  have hpos := fun τ => tiltedIntegral_pos hμ hw hw0 hf hg hfM hgM τ
  have hc1 : ∀ (G : α → ℝ), AEStronglyMeasurable G μ → (∃ K : ℝ, ∀ᵐ a ∂μ, |G a| ≤ K) →
      Continuous (tiltedMean μ w f g G) := by
    rintro G hG ⟨K, hK⟩
    unfold tiltedMean
    have hden := continuous_tiltedIntegral hw hf hg hfM hgM (G := fun _ => (1 : ℝ))
      aestronglyMeasurable_const (K := 1) (by simp)
    simp only [one_mul] at hden
    exact (continuous_tiltedIntegral hw hf hg hfM hgM hG hK).div hden fun τ => (hpos τ).ne'
  refine ⟨hpos, hc1, ?_⟩
  have hder : ∀ τ ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt
      (fun τ : ℝ => Real.log (∫ a, w a * Real.exp (f a + τ * g a) ∂μ))
      (tiltedMean μ w f g g τ) τ := by
    intro τ _
    exact (hasDerivAt_tiltedIntegral hw hf hg hfM hgM τ).log (hpos τ).ne'
  have hcont := hc1 g hg ⟨M, hgM⟩
  have := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hcont.intervalIntegrable 0 1)
  simpa using this.symm
end YangMills.Construction.Interpolation
end
