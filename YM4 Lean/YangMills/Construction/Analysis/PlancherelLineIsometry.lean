import YangMills.Construction.Analysis.PlancherelLine
import Mathlib
open MeasureTheory FourierTransform
open scoped ContDiff
set_option autoImplicit false
namespace YangMills.Construction.Analysis.Plancherel
theorem continuous_fourierIntegral {u : ℝ → ℂ} (hu : Integrable u) :
    Continuous (𝓕 u : ℝ → ℂ) :=
  VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    continuous_inner hu
theorem fourierIntegral_ae_eq_fourierLp {u : ℝ → ℂ} (hu : Integrable u)
    (hu2 : MemLp u 2 (volume : Measure ℝ)) :
    (𝓕 u : ℝ → ℂ) =ᵐ[volume] (𝓕 (hu2.toLp u) : Lp ℂ 2 (volume : Measure ℝ)) := by
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu2.toLp u) with hF
  refine ae_eq_of_integral_contDiff_smul_eq (μ := volume) ?_ ?_ ?_
  · exact (continuous_fourierIntegral hu).locallyIntegrable
  · exact (Lp.memLp F).locallyIntegrable (by norm_num)
  intro ψ hψ hψs
  have hΨ : ContDiff ℝ ∞ (fun x => (ψ x : ℂ)) := Complex.ofRealCLM.contDiff.comp hψ
  have hΨs : HasCompactSupport (fun x => (ψ x : ℂ)) :=
    hψs.comp_left (g := fun x : ℝ => (x : ℂ)) (by simp)
  let Ψ : SchwartzMap ℝ ℂ := hΨs.toSchwartzMap hΨ
  have hΨa : ∀ x, Ψ x = (ψ x : ℂ) := fun x => rfl
  have h₁ : ∫ x, ψ x • (𝓕 u) x = ∫ x, (𝓕 Ψ) x • u x := by
    have hswap : ∫ x, (𝓕 Ψ) x • u x = ∫ x, Ψ x • (𝓕 u) x := by
      rw [SchwartzMap.fourier_coe]
      simpa using! VectorFourier.integral_bilin_fourierIntegral_eq_flip
        (ContinuousLinearMap.lsmul ℂ ℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ) (L := innerₗ ℝ)
        Real.continuous_fourierChar continuous_inner (Ψ.integrable (μ := volume)) hu
    rw [hswap]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [hΨa]
  have h₂ : ∫ x, ψ x • F x = ∫ x, (𝓕 Ψ) x • u x := by
    have hl : ∫ x, ψ x • F x = Lp.toTemperedDistribution F Ψ := by
      rw [Lp.toTemperedDistribution_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [hΨa]
    have hr : Lp.toTemperedDistribution F Ψ
        = Lp.toTemperedDistribution (hu2.toLp u) (𝓕 Ψ) := by
      rw [hF, ← Lp.fourier_toTemperedDistribution_eq, TemperedDistribution.fourier_apply]
    rw [hl, hr, Lp.toTemperedDistribution_apply]
    refine integral_congr_ae ?_
    filter_upwards [hu2.coeFn_toLp] with x hx
    rw [hx]
  rw [h₁, h₂]
theorem L2_norm_sq_eq_integral (f : Lp ℂ 2 (volume : Measure ℝ)) :
    ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ) f, L2.inner_def (𝕜 := ℂ) f f,
    ← integral_re (L2.integrable_inner (𝕜 := ℂ) f f)]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
    (norm_sq_eq_re_inner (𝕜 := ℂ) (f x)).symm)
theorem integral_norm_sq_fourierIntegral {u : ℝ → ℂ} (hu : Integrable u)
    (hu2 : MemLp u 2 (volume : Measure ℝ)) :
    Integrable (fun x => ‖(𝓕 u : ℝ → ℂ) x‖ ^ 2) ∧
      ∫ x, ‖(𝓕 u : ℝ → ℂ) x‖ ^ 2 = ∫ x, ‖u x‖ ^ 2 := by
  have hae := fourierIntegral_ae_eq_fourierLp hu hu2
  set F : Lp ℂ 2 (volume : Measure ℝ) := 𝓕 (hu2.toLp u) with hF
  have hnorm : ∀ᵐ x, ‖(𝓕 u : ℝ → ℂ) x‖ ^ 2 = ‖F x‖ ^ 2 := by
    filter_upwards [hae] with x hx
    rw [hx]
  constructor
  · have hint : Integrable (fun x => ‖F x‖ ^ 2) :=
      MemLp.integrable_norm_pow (p := 2) (by simpa using Lp.memLp F) (by norm_num)
    exact hint.congr (hnorm.mono fun x hx => hx.symm)
  · rw [integral_congr_ae hnorm, ← L2_norm_sq_eq_integral, hF, Lp.norm_fourier_eq,
      L2_norm_sq_eq_integral]
    refine integral_congr_ae ?_
    filter_upwards [hu2.coeFn_toLp] with x hx
    rw [hx]
theorem integral_mul_exp_eq_fourierIntegral (u : ℝ → ℂ) (ξ : ℝ) :
    ∫ t : ℝ, u t * Complex.exp (Complex.I * t * ξ)
      = (𝓕 u : ℝ → ℂ) (-(2 * Real.pi)⁻¹ * ξ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hexp : (↑(-2 * Real.pi * t * (-(2 * Real.pi)⁻¹ * ξ)) * Complex.I : ℂ)
      = Complex.I * t * ξ := by
    push_cast
    field_simp
  beta_reduce
  rw [hexp, smul_eq_mul, mul_comm]
theorem plancherelRealLine_holds : PlancherelRealLine := by
  intro u hc hs
  have hu : Integrable u := hc.integrable_of_hasCompactSupport hs
  have hu2 : MemLp u 2 (volume : Measure ℝ) := hc.memLp_of_hasCompactSupport hs
  obtain ⟨hint, heq⟩ := integral_norm_sq_fourierIntegral hu hu2
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hscale : -(2 * Real.pi)⁻¹ ≠ 0 := by simp [hpi]
  simp_rw [integral_mul_exp_eq_fourierIntegral]
  refine ⟨hint.comp_mul_left' hscale, ?_⟩
  rw [Measure.integral_comp_mul_left (fun x => ‖(𝓕 u : ℝ → ℂ) x‖ ^ 2), heq]
  have habs : |(-(2 * Real.pi)⁻¹)⁻¹| = 2 * Real.pi := by
    rw [inv_neg, inv_inv, abs_neg, abs_of_pos (by positivity)]
  rw [habs, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
end YangMills.Construction.Analysis.Plancherel
