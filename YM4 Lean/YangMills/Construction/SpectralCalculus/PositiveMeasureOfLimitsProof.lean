import YangMills.Construction.SpectralCalculus.JointSpectralMeasure
import YangMills.Construction.SpectralCalculus.PositiveMeasureOfLimits
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology ComplexOrder
noncomputable section
namespace YangMills.Construction.SpectralCalculus
section Positive
variable {α : Type*} [MeasurableSpace α]
theorem apply_eq_ofReal_variation_real (μ : ComplexMeasure α) (hμ : ∀ B, MeasurableSet B → 0 ≤ μ B)
    {B : Set α} (hB : MeasurableSet B) : μ B = ((μ.variation.real B : ℝ) : ℂ) := by
  have hre : ∀ E, MeasurableSet E → 0 ≤ (μ E).re := fun E hE => (Complex.le_def.mp (hμ E hE)).1
  have him : ∀ E, MeasurableSet E → (μ E).im = 0 := fun E hE => (Complex.le_def.mp (hμ E hE)).2.symm
  have hle : (0 : SignedMeasure α) ≤[univ] ComplexMeasure.re μ :=
    VectorMeasure.restrict_le_restrict_of_subset_le _ _ fun E hE _ => by
      rw [zero_apply]
      exact hre E hE
  let m : Measure α := (ComplexMeasure.re μ).toMeasureOfZeroLE univ MeasurableSet.univ hle
  have hm : ∀ E, MeasurableSet E → m E = ‖μ E‖ₑ := fun E hE => by
    have h₁ : m E = ENNReal.ofReal (μ E).re := by
      simp only [m]
      rw [SignedMeasure.toMeasureOfZeroLE_apply _ hle MeasurableSet.univ hE]
      rw [← ENNReal.ofReal_coe_nnreal]
      simp only [univ_inter, NNReal.coe_mk]
      rfl
    have h₂ : μ E = (((μ E).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him E hE])
    rw [h₁, ← ofReal_norm, h₂, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by simpa using hre E hE)]
    simp
  have hv : μ.variation = m := le_antisymm
    (VectorMeasure.variation_le_of_forall_enorm_le fun E hE => (hm E hE).ge)
    (Measure.le_intro fun E hE _ => (hm E hE).le.trans (VectorMeasure.enorm_measure_le_variation μ E))
  have h₃ : μ.variation.real B = (μ B).re := by
    rw [Measure.real, hv, hm B hB, ← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _)]
    have h₂ : μ B = (((μ B).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him B hB])
    rw [h₂, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by simpa using hre B hB)]
    simp
  rw [h₃]
  exact Complex.ext (by simp) (by simp [him B hB])
theorem complexIntegral_eq_integral_variation (μ : ComplexMeasure α)
    (hμ : ∀ B, MeasurableSet B → 0 ≤ μ B) (F : α → ℂ) :
    complexIntegral μ F = ∫ x, F x ∂μ.variation := by
  unfold complexIntegral
  rw [VectorMeasure.integral_eq_setToFun, MeasureTheory.integral_eq_setToFun]
  refine setToFun_congr_left' _ _ (fun s hs _ => ContinuousLinearMap.ext fun x => ?_) F
  have h₁ : (μ.transpose mulPairing s) x = x * μ s := rfl
  rw [h₁, weightedSMul_apply, apply_eq_ofReal_variation_real μ hμ hs]
  simp [mul_comm]
end Positive
section Limits
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
theorem tendsto_prod_fst_atTop_nat : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_fst
theorem tendsto_prod_snd_atTop_nat : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
  rw [← prod_atTop_atTop_eq]
  exact tendsto_snd
theorem tendsto_prodMk_atTop_nat {a b : ℕ × ℕ → ℕ} (ha : Tendsto a atTop atTop)
    (hb : Tendsto b atTop atTop) : Tendsto (fun p => (a p, b p)) atTop atTop :=
  (ha.prodMk hb).mono_right prod_atTop_atTop_eq.le
omit [CompleteSpace H] in
theorem cauchySeq_of_tendsto_inner_prod {x : ℕ → H} {L : ℂ}
    (h : Tendsto (fun p : ℕ × ℕ => inner ℂ (x p.1) (x p.2)) atTop (𝓝 L)) : CauchySeq x := by
  have h₁₁ := h.comp (tendsto_prodMk_atTop_nat tendsto_prod_fst_atTop_nat tendsto_prod_fst_atTop_nat)
  have h₁₂ := h.comp (tendsto_prodMk_atTop_nat tendsto_prod_fst_atTop_nat tendsto_prod_snd_atTop_nat)
  have h₂₁ := h.comp (tendsto_prodMk_atTop_nat tendsto_prod_snd_atTop_nat tendsto_prod_fst_atTop_nat)
  have h₂₂ := h.comp (tendsto_prodMk_atTop_nat tendsto_prod_snd_atTop_nat tendsto_prod_snd_atTop_nat)
  have hs : Tendsto (fun p : ℕ × ℕ => ((inner ℂ (x p.1) (x p.1) - inner ℂ (x p.1) (x p.2) -
      inner ℂ (x p.2) (x p.1) + inner ℂ (x p.2) (x p.2) : ℂ)).re) atTop (𝓝 0) := by
    have := (((h₁₁.sub h₁₂).sub h₂₁).add h₂₂)
    have h0 := (Complex.continuous_re.tendsto _).comp this
    simpa [Function.comp_def] using h0
  have hd : Tendsto (fun p : ℕ × ℕ => ‖x p.1 - x p.2‖ ^ 2) atTop (𝓝 0) := by
    refine hs.congr fun p => ?_
    have e : ∀ y : H, (inner ℂ y y : ℂ).re = ‖y‖ ^ 2 := fun y => inner_self_eq_norm_sq (𝕜 := ℂ) y
    have hc : (inner ℂ (x p.2) (x p.1)).re = (inner ℂ (x p.1) (x p.2)).re :=
      inner_re_symm (𝕜 := ℂ) _ _
    rw [@norm_sub_sq ℂ]
    simp only [Complex.sub_re, Complex.add_re, e, RCLike.re_to_complex]
    rw [hc]
    ring
  refine cauchySeq_iff_tendsto_dist_atTop_0.mpr ?_
  simpa [dist_eq_norm, Real.sqrt_sq (norm_nonneg _)] using hd.sqrt
theorem exists_tendsto_semigroup_apply_of_tendsto_inner {T : ℝ≥0 → H →L[ℂ] H} {U : ℝ → H →L[ℂ] H}
    {v : ℕ → H} {g : ℝ≥0 → ℝ → ℂ} (hTU : IsCommutingSemigroupGroup T U)
    (hlim : ∀ t₀ : ℝ≥0, 0 < t₀ → ∀ (t : ℝ≥0) (s : ℝ),
      Tendsto (fun p : ℕ × ℕ => inner ℂ (T t₀ (v p.1)) (T t (U s (T t₀ (v p.2))))) atTop
        (𝓝 (g (2 * t₀ + t) s)))
    {t₀ : ℝ≥0} (ht₀ : 0 < t₀) :
    ∃ w : H, Tendsto (fun n => T t₀ (v n)) atTop (𝓝 w) ∧
      ∀ (t : ℝ≥0) (s : ℝ), inner ℂ w (T t (U s w)) = g (2 * t₀ + t) s := by
  have h0 := hlim t₀ ht₀ 0 0
  simp only [hTU.semigroup.map_zero, hTU.group.map_zero,
    one_apply_eq_self] at h0
  obtain ⟨w, hw⟩ :=
    cauchySeq_tendsto_of_complete (cauchySeq_of_tendsto_inner_prod (x := fun n => T t₀ (v n)) h0)
  refine ⟨w, hw, fun t s => ?_⟩
  have hA : Continuous fun y : H => T t (U s y) := (T t).continuous.comp (U s).continuous
  have h₁ : Tendsto (fun p : ℕ × ℕ => inner ℂ (T t₀ (v p.1)) (T t (U s (T t₀ (v p.2))))) atTop
      (𝓝 (inner ℂ w (T t (U s w)))) :=
    (hw.comp tendsto_prod_fst_atTop_nat).inner
      ((hA.tendsto w).comp (hw.comp tendsto_prod_snd_atTop_nat))
  exact tendsto_nhds_unique h₁ (hlim t₀ ht₀ t s)
end Limits
theorem measurable_expNegTwoMul (t : ℝ≥0) : Measurable (expNegTwoMul t) := by
  unfold expNegTwoMul
  fun_prop
theorem norm_expNegTwoMul (t : ℝ≥0) (p : SpectralPlane) :
    ‖expNegTwoMul t p‖ = Real.exp (-2 * (t : ℝ) * (p.1 : ℝ)) := by
  unfold expNegTwoMul
  rw [Complex.norm_exp]
  simp
theorem positiveSpectralMeasureOfLimits_proof (hJ : JointSpectralTheorem) :
    PositiveSpectralMeasureOfLimits := by
  intro H _ _ _ T U v g hTU _ hlim
  have facts := hJ H T U hTU
  obtain ⟨w₁, hw₁, -⟩ := exists_tendsto_semigroup_apply_of_tendsto_inner hTU hlim (t₀ := 1) one_pos
  let D : SpectralPlane → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (2 * (p.1 : ℝ)))
  have hD : Measurable D := by
    simp only [D]
    fun_prop
  refine ⟨(pairSpectralMeasure T U w₁ w₁).variation.withDensity D, fun t ht => ?_⟩
  obtain ⟨t₀, ht₀, ht₁, ht₂⟩ : ∃ t₀ : ℝ≥0, 0 < t₀ ∧ t₀ ≤ 1 ∧ 2 * t₀ ≤ t := by
    refine ⟨min 1 (t / 4), lt_min one_pos (by positivity), min_le_left _ _, ?_⟩
    have h₁ : min 1 (t / 4) ≤ t / 4 := min_le_right _ _
    calc 2 * min 1 (t / 4) ≤ 2 * (t / 4) := by gcongr
      _ = t / 2 := by ring
      _ ≤ t := by
        rw [← NNReal.coe_le_coe]
        push_cast
        have : (0 : ℝ) ≤ t := t.2
        linarith
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, a + t₀ = 1 := ⟨1 - t₀, tsub_add_cancel_of_le ht₁⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, 2 * t₀ + b = t := ⟨t - 2 * t₀, add_tsub_cancel_of_le ht₂⟩
  have ha' : (a : ℝ) + t₀ = 1 := by exact_mod_cast ha
  have hb' : 2 * (t₀ : ℝ) + b = t := by exact_mod_cast hb
  obtain ⟨w, hw, hg⟩ := exists_tendsto_semigroup_apply_of_tendsto_inner hTU hlim ht₀
  have hTa : T a w = w₁ := by
    have h₁ : Tendsto (fun n => T a (T t₀ (v n))) atTop (𝓝 (T a w)) :=
      ((T a).continuous.tendsto w).comp hw
    refine tendsto_nhds_unique (h₁.congr fun n => ?_) hw₁
    have := congrArg (fun B : H →L[ℂ] H => B (v n)) (hTU.semigroup.map_add a t₀)
    simpa [ha] using this
  let μ := pairSpectralMeasure T U w w
  have hμ : ∀ B, MeasurableSet B → 0 ≤ μ B := fun B hB => facts.nonneg w ⟨B, hB⟩
  have hint : VectorMeasure.Integrable μ (expNegTwoMul a) := by
    refine Integrable.of_bound (measurable_expNegTwoMul a).aestronglyMeasurable 1
      (Eventually.of_forall fun p => ?_)
    rw [norm_expNegTwoMul, Real.exp_le_one_iff]
    have h₁ : (0 : ℝ) ≤ a := a.2
    have h₂ : (0 : ℝ) ≤ p.1 := p.1.2
    nlinarith [mul_nonneg h₁ h₂]
  have hvar : (pairSpectralMeasure T U w₁ w₁).variation =
      μ.variation.withDensity fun p => ‖expNegTwoMul a p‖ₑ := by
    have hB : ∀ x y : ℂ, ‖mulPairing x y‖₊ = ‖x‖₊ * ‖y‖₊ := fun x y => by simp
    rw [← hTa, facts.both_eq_density w a, withDensityComplex,
      VectorMeasure.variation_withDensity hint hB, VectorMeasure.variation_transpose_eq μ mulPairing hB]
  let D' : SpectralPlane → ℝ≥0∞ := fun p => ENNReal.ofReal (Real.exp (2 * (t₀ : ℝ) * (p.1 : ℝ)))
  have hD' : Measurable D' := by
    simp only [D']
    fun_prop
  have hρ : (pairSpectralMeasure T U w₁ w₁).variation.withDensity D = μ.variation.withDensity D' := by
    rw [hvar, ← withDensity_mul _ (measurable_expNegTwoMul a).enorm hD]
    congr 1
    funext p
    simp only [Pi.mul_apply, D, D']
    rw [← ofReal_norm, norm_expNegTwoMul,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    have h₁ : (t₀ : ℝ) = 1 - a := by linarith
    rw [h₁]
    ring
  rw [hρ]
  constructor
  · rw [lintegral_withDensity_eq_lintegral_mul _ hD' (by fun_prop)]
    refine lt_of_le_of_lt (lintegral_mono (g := fun _ => 1) fun p => ?_) ?_
    · simp only [Pi.mul_apply, D']
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      refine ENNReal.ofReal_le_one.mpr (Real.exp_le_one_iff.mpr ?_)
      have h₁ : (0 : ℝ) ≤ b := b.2
      have h₂ : (0 : ℝ) ≤ p.1 := p.1.2
      rw [← hb']
      nlinarith [mul_nonneg h₁ h₂]
    · simp
  · intro s
    rw [integral_withDensity_eq_integral_toReal_smul hD' (Eventually.of_forall fun p => by simp [D'])]
    have h₁ : inner ℂ w (T b (U s w)) = complexIntegral μ (spectralCharacter b s) :=
      facts.hasSpectralTransform w w b s
    rw [← hb, ← hg b s, h₁, complexIntegral_eq_integral_variation μ hμ]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [D']
    rw [ENNReal.toReal_ofReal (Real.exp_pos _).le]
    unfold spectralCharacter
    rw [Complex.real_smul, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
end YangMills.Construction.SpectralCalculus
end
