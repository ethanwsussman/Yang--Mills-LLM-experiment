import YangMills.Construction.SummableBoundsOfTheFlow.MeanAlongAField
import Mathlib
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped RealInnerProductSpace
namespace YangMills.Construction.BondIntegration
open MeasureTheory ColdStepAtMirrorFrames
variable {ι : Type} [Fintype ι] [DecidableEq ι] {ρ : ℝ} {p : ℝ → ℝ}
theorem hasDerivAt_norm_add_smul {v e : BondVector} (hv : v ≠ 0) :
    HasDerivAt (fun τ : ℝ => ‖v + τ • e‖) (‖v‖⁻¹ * ⟪v, e⟫) 0 := by
  have hsq : HasDerivAt (fun τ : ℝ => ‖v‖ ^ 2 + 2 * τ * ⟪v, e⟫ + τ ^ 2 * ‖e‖ ^ 2) (2 * ⟪v, e⟫) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => 2 * τ * ⟪v, e⟫) (2 * ⟪v, e⟫) 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const (⟪v, e⟫)
      simpa using this
    have h2 : HasDerivAt (fun τ : ℝ => τ ^ 2 * ‖e‖ ^ 2) 0 0 := by
      have := ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const (‖e‖ ^ 2)
      simpa using this
    have := ((hasDerivAt_const (0 : ℝ) (‖v‖ ^ 2)).add h1).add h2
    exact this.congr_deriv (by simp)
  have hne : ‖v‖ ^ 2 + 2 * (0 : ℝ) * ⟪v, e⟫ + (0 : ℝ) ^ 2 * ‖e‖ ^ 2 ≠ 0 := by
    have : 0 < ‖v‖ := norm_pos_iff.2 hv
    simp only [mul_zero, zero_mul, add_zero]
    positivity
  have hs := hsq.sqrt hne
  have e1 : (fun τ : ℝ => Real.sqrt (‖v‖ ^ 2 + 2 * τ * ⟪v, e⟫ + τ ^ 2 * ‖e‖ ^ 2)) =
      fun τ => ‖v + τ • e‖ := by
    funext τ
    have : ‖v + τ • e‖ ^ 2 = ‖v‖ ^ 2 + 2 * τ * ⟪v, e⟫ + τ ^ 2 * ‖e‖ ^ 2 := by
      rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow]
      simp only [Real.norm_eq_abs, sq_abs]
      ring
    rw [← this, Real.sqrt_sq (norm_nonneg _)]
  rw [e1] at hs
  refine HasDerivAt.congr_deriv hs ?_
  have hp : 0 < ‖v‖ := norm_pos_iff.2 hv
  have e2 : ‖v‖ ^ 2 + 2 * (0 : ℝ) * ⟪v, e⟫ + (0 : ℝ) ^ 2 * ‖e‖ ^ 2 = ‖v‖ ^ 2 := by ring
  rw [e2, Real.sqrt_sq hp.le]
  field_simp
theorem hasDerivAt_cutoffFactor_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {v : BondVector} (hv : ‖v‖ < ρ)
    (e : BondVector) :
    HasDerivAt (fun τ : ℝ => cutoffFactor ρ p ‖v + τ • e‖)
      (-(cutoffFactor ρ p ‖v‖ * radialCutoffSlope p v e)) 0 := by
  by_cases h0 : v = 0
  · subst h0
    have hev : (fun τ : ℝ => cutoffFactor ρ p ‖(0 : BondVector) + τ • e‖) =ᶠ[nhds 0] fun _ => 1 := by
      have hc : Continuous fun τ : ℝ => ‖(0 : BondVector) + τ • e‖ := by fun_prop
      have hlt : ∀ᶠ τ in nhds (0 : ℝ), ‖(0 : BondVector) + τ • e‖ < 5 * ρ / 8 := by
        have : ‖(0 : BondVector) + (0 : ℝ) • e‖ < 5 * ρ / 8 := by simp; positivity
        exact hc.continuousAt.eventually_lt continuousAt_const this
      filter_upwards [hlt] with τ hτ
      have h1 : ‖(0 : BondVector) + τ • e‖ < ρ := by linarith
      unfold cutoffFactor
      rw [if_pos h1, hp.vanish_small _ (norm_nonneg _) hτ.le]
      simp
    have := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).congr_of_eventuallyEq hev
    refine HasDerivAt.congr_deriv this ?_
    simp [radialCutoffSlope]
  · have hpos : 0 < ‖v‖ := norm_pos_iff.2 h0
    have hn := hasDerivAt_norm_add_smul (e := e) h0
    have hsm : HasDerivAt p (deriv p ‖v‖) ‖v‖ :=
      ((hp.smooth.contDiffAt (Ico_mem_nhds hpos hv)).differentiableAt (by simp)).hasDerivAt
    have hcomp : HasDerivAt (fun τ : ℝ => p ‖v + τ • e‖) (deriv p ‖v‖ * (‖v‖⁻¹ * ⟪v, e⟫)) 0 := by
      have h2 : HasDerivAt p (deriv p ‖v‖) ‖v + (0 : ℝ) • e‖ := by simpa using hsm
      exact h2.comp (0 : ℝ) hn
    have hexp := hcomp.neg.exp
    have hev : (fun τ : ℝ => cutoffFactor ρ p ‖v + τ • e‖) =ᶠ[nhds 0]
        fun τ => Real.exp (-(p ‖v + τ • e‖)) := by
      have hc : Continuous fun τ : ℝ => ‖v + τ • e‖ := by fun_prop
      have hlt : ∀ᶠ τ in nhds (0 : ℝ), ‖v + τ • e‖ < ρ :=
        hc.continuousAt.eventually_lt continuousAt_const (by simpa using hv)
      filter_upwards [hlt] with τ hτ
      unfold cutoffFactor
      rw [if_pos hτ]
    have h3 := hexp.congr_of_eventuallyEq hev
    refine HasDerivAt.congr_deriv h3 ?_
    have : cutoffFactor ρ p ‖v‖ = Real.exp (-(p ‖v‖)) := by
      unfold cutoffFactor
      rw [if_pos hv]
    simp only [Pi.neg_apply, zero_smul, add_zero, radialCutoffSlope, this]
    ring
theorem add_smul_bondVariation_apply (η : BondField ι) (b : ι) (e : BondVector) (τ : ℝ) (b' : ι) :
    (η + τ • bondVariation b e) b' = if b' = b then η b + τ • e else η b' := by
  by_cases h : b' = b
  · subst h
    simp [bondVariation]
  · simp [bondVariation, h, Pi.single_eq_of_ne h]
theorem hasDerivAt_ballDensity_line (hρ : 0 < ρ) (hp : IsCutoff ρ p) {Ψ : BondField ι → ℝ} {η : BondField ι}
    (hη : ∀ b, ‖η b‖ < ρ) (hΨ : DifferentiableAt ℝ Ψ η) (b : ι) (e : BondVector) :
    HasDerivAt (fun τ : ℝ => ballDensity (cutoffFactor ρ p) Ψ (η + τ • bondVariation b e))
      (-(ballDensity (cutoffFactor ρ p) Ψ η *
        (fderiv ℝ Ψ η (bondVariation b e) + radialCutoffSlope p (η b) e))) 0 := by
  set rest : ℝ := ∏ b' ∈ Finset.univ.erase b, cutoffFactor ρ p ‖η b'‖ with hrest
  have hprod : ∀ τ : ℝ, radialWeightProd (cutoffFactor ρ p) (η + τ • bondVariation b e) =
      cutoffFactor ρ p ‖η b + τ • e‖ * rest := by
    intro τ
    unfold radialWeightProd
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ b), add_smul_bondVariation_apply]
    simp only [if_true, hrest]
    congr 1
    refine Finset.prod_congr rfl fun b' hb' => ?_
    rw [add_smul_bondVariation_apply, if_neg (Finset.ne_of_mem_erase hb')]
  have hprod0 : radialWeightProd (cutoffFactor ρ p) η = cutoffFactor ρ p ‖η b‖ * rest := by
    have := hprod 0
    simpa using this
  have hline : HasDerivAt (fun τ : ℝ => Ψ (η + τ • bondVariation b e))
      (fderiv ℝ Ψ η (bondVariation b e)) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => η + τ • bondVariation b e) (bondVariation b e) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e)).const_add η
    have h2 : HasFDerivAt Ψ (fderiv ℝ Ψ η) (η + (0 : ℝ) • bondVariation b e) := by
      simpa using hΨ.hasFDerivAt
    exact h2.comp_hasDerivAt (0 : ℝ) h1
  have h1 := (hasDerivAt_cutoffFactor_line hρ hp (hη b) e).mul_const rest
  have h2 := hline.neg.exp
  have h3 := h1.mul h2
  have e1 : (fun τ : ℝ => ballDensity (cutoffFactor ρ p) Ψ (η + τ • bondVariation b e)) =
      fun τ => cutoffFactor ρ p ‖η b + τ • e‖ * rest * Real.exp (-(Ψ (η + τ • bondVariation b e))) := by
    funext τ
    unfold ballDensity
    rw [hprod]
  rw [e1]
  refine HasDerivAt.congr_deriv h3 ?_
  unfold ballDensity
  rw [hprod0]
  simp only [Pi.neg_apply, zero_smul, add_zero]
  ring
theorem integralAlongField_of_integralByParts (hby : IntegralByPartsAtBond) :
    integralAlongFieldStatement := by
  intro ι _ _ ρ p Ψ G b z C hρ hp hΨ hG hz hzC hdC hv hi hdi hA hS
  set W := ballDensity (cutoffFactor ρ p) Ψ with hW
  set u : BondField ι → ℝ := fun η => G η * W η with hu
  have key := hby ι b z u C hz hzC hdC hv.differentiable hi hdi
  have hopen : IsOpen {η : BondField ι | ∀ b, ‖η b‖ < ρ} := by
    have : {η : BondField ι | ∀ b, ‖η b‖ < ρ} = ⋂ b, {η | ‖η b‖ < ρ} := by
      ext η
      simp
    rw [this]
    exact isOpen_iInter_of_finite fun b =>
      isOpen_lt (continuous_norm.comp (continuous_apply b)) continuous_const
  have hder : ∀ η, (∀ b, ‖η b‖ < ρ) → ∀ e : BondVector,
      fderiv ℝ u η (bondVariation b e) = fderiv ℝ G η (bondVariation b e) * W η +
        G η * (-(W η * (fderiv ℝ Ψ η (bondVariation b e) + radialCutoffSlope p (η b) e))) := by
    intro η hη e
    have hGd : DifferentiableAt ℝ G η :=
      (hG.contDiffAt (hopen.mem_nhds hη)).differentiableAt (by norm_num)
    have hΨd : DifferentiableAt ℝ Ψ η :=
      (hΨ.contDiffAt (hopen.mem_nhds hη)).differentiableAt (by norm_num)
    have hl : HasDerivAt (fun τ : ℝ => η + τ • bondVariation b e) (bondVariation b e) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bondVariation b e)).const_add η
    have hGl : HasDerivAt (fun τ : ℝ => G (η + τ • bondVariation b e))
        (fderiv ℝ G η (bondVariation b e)) 0 := by
      have h2 : HasFDerivAt G (fderiv ℝ G η) (η + (0 : ℝ) • bondVariation b e) := by
        simpa using hGd.hasFDerivAt
      exact h2.comp_hasDerivAt (0 : ℝ) hl
    have hul : HasDerivAt (fun τ : ℝ => u (η + τ • bondVariation b e))
        (fderiv ℝ u η (bondVariation b e)) 0 := by
      have h2 : HasFDerivAt u (fderiv ℝ u η) (η + (0 : ℝ) • bondVariation b e) := by
        simpa using (hv.differentiable η).hasFDerivAt
      exact h2.comp_hasDerivAt (0 : ℝ) hl
    have hprod := hGl.mul (hasDerivAt_ballDensity_line hρ hp hη hΨd b e)
    have e0 : G (η + (0 : ℝ) • bondVariation b e) = G η := by simp
    have e1 : ballDensity (cutoffFactor ρ p) Ψ (η + (0 : ℝ) • bondVariation b e) = W η := by simp [hW]
    rw [e0, e1] at hprod
    exact hul.unique hprod
  have hpt : ∀ η, fderiv ℝ u η (bondVariation b (z (η b))) + bondDivergence z (η b) * u η =
      fieldDerivative b z G η * W η - G η * fieldScore p Ψ b z η * W η := by
    intro η
    by_cases hη : ∀ b, ‖η b‖ < ρ
    · rw [hder η hη]
      simp only [hu, fieldDerivative, fieldScore, bondPartialDeriv]
      ring
    · have h0 : W η = 0 := by
        obtain ⟨c, hc⟩ := not_forall.1 hη
        simp only [hW, ballDensity, radialWeightProd]
        have : ∏ b', cutoffFactor ρ p ‖η b'‖ = 0 := by
          refine Finset.prod_eq_zero (Finset.mem_univ c) ?_
          unfold cutoffFactor
          rw [if_neg hc]
        rw [this, zero_mul]
      rw [hv.fderiv_eq_zero_outside η hη]
      simp [hu, h0]
  have hint : ∫ η, (fieldDerivative b z G η * W η - G η * fieldScore p Ψ b z η * W η) = 0 := by
    rw [← key]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => (hpt η).symm)
  rw [integral_sub hA hS] at hint
  linarith
end YangMills.Construction.BondIntegration
end
