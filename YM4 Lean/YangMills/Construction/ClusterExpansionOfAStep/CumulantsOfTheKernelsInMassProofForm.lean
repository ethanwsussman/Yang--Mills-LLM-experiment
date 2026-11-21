import YangMills.Construction.ClusterExpansionOfAStep.CumulantsOfTheKernelsInMass
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
open MeasureTheory
namespace YangMills.Construction.TorusLumps
open BlockAverages LumpContours TorusFields
namespace KernelMass
theorem continuous_re_coe_unitQuaternion :
    Continuous fun g : UnitQuaternion => ((g : UnitQuaternion) : ℍ[ℝ]).re :=
  Quaternion.continuous_re.comp continuous_subtype_val
theorem zero_lt_partitionFn (s : ℝ) : 0 < partitionFn s := by
  unfold partitionFn
  refine integral_exp_pos ?_
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_re_coe_unitQuaternion) |>.comp
    continuous_id).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _) |>.congr
      (Filter.Eventually.of_forall fun _ => rfl)
theorem zero_lt_bondKernel (ℓ : StepParameters) (x : ℝ) {n : ℕ}
    (W : (stepBlockFrame ℓ.side n).GaugeField 0)
    (V : (stepBlockFrame ℓ.side n).GaugeField 1)
    (b : (stepBlockFrame ℓ.side n).Cell → (stepBlockFrame ℓ.side n).Site 0)
    (c : (stepBlockFrame ℓ.side n).Cell × Fin 4) : 0 < bondKernel ℓ x W V b c :=
  div_pos (Real.exp_pos _) (zero_lt_partitionFn _)
end KernelMass
open KernelMass in
theorem KernelMassCumulantBound.of_kernelCumulantBound (hB : KernelCumulantBound) :
    KernelMassCumulantBound := by
  intro ℓ x n _ Ξ _ μ ρ W b V hs hρ hm hk hpos k c X
  let K : TorusField n → Ξ → ℝ := fun V' ξ => ∏ c' : (stepBlockFrame ℓ.side n).Cell × Fin 4,
    bondKernel ℓ x (W ξ) (readAtLevel (stepBlockFrame ℓ.side n) 1 V') (b ξ) c'
  have hKpos : ∀ V' ξ, 0 < K V' ξ := fun V' ξ =>
    Finset.prod_pos fun c' _ => zero_lt_bondKernel ℓ x _ _ _ _
  have hKm : ∀ V', Measurable (K V') := fun V' =>
    Finset.measurable_fun_prod _ fun c' _ => hk V' c'
  have hfin : (∫⁻ ξ, ρ ξ * ENNReal.ofReal (K V ξ) ∂μ) ≠ ⊤ := by
    intro h
    have : kernelMass ℓ x μ ρ W b V = 0 := by
      show (∫⁻ ξ, ρ ξ * ENNReal.ofReal (K V ξ) ∂μ).toReal = 0
      rw [h]
      rfl
    exact hpos.ne' this
  have hae : ∀ᵐ ξ ∂μ, ρ ξ < ⊤ := by
    have h1 := ae_lt_top (hρ.mul (hKm V).ennreal_ofReal) hfin
    filter_upwards [h1] with ξ hξ
    by_contra hcon
    have h2 : ρ ξ = ⊤ := top_le_iff.mp (not_lt.mp hcon)
    have h3 : ENNReal.ofReal (K V ξ) ≠ 0 := by
      simpa using hKpos V ξ
    rw [Pi.mul_apply, h2, ENNReal.top_mul h3] at hξ
    exact lt_irrefl _ hξ
  let A : Ξ → ℝ := fun ξ => (ρ ξ).toReal
  have hAm : Measurable A := hρ.ennreal_toReal
  have hA0 : ∀ ξ, 0 ≤ A ξ := fun ξ => ENNReal.toReal_nonneg
  have hofReal : ∀ V', (fun ξ => ENNReal.ofReal (A ξ * K V' ξ)) =ᵐ[μ]
      fun ξ => ρ ξ * ENNReal.ofReal (K V' ξ) := by
    intro V'
    filter_upwards [hae] with ξ hξ
    rw [ENNReal.ofReal_mul (hA0 ξ), ENNReal.ofReal_toReal hξ.ne]
  have hmean : ∀ V', kernelProductMean ℓ x μ A W b V' = kernelMass ℓ x μ ρ W b V' := by
    intro V'
    show (∫ ξ, A ξ * K V' ξ ∂μ) = (∫⁻ ξ, ρ ξ * ENNReal.ofReal (K V' ξ) ∂μ).toReal
    rw [integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun ξ => mul_nonneg (hA0 ξ) (hKpos V' ξ).le)
      (hAm.mul (hKm V')).aestronglyMeasurable, lintegral_congr_ae (hofReal V')]
  have hint : Integrable (fun ξ => A ξ * K V ξ) μ := by
    refine ⟨(hAm.mul (hKm V)).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun ξ => mul_nonneg (hA0 ξ) (hKpos V ξ).le),
      lintegral_congr_ae (hofReal V)]
    exact lt_top_iff_ne_top.mpr hfin
  have hB' := hB ℓ x n Ξ μ A W b V hs hA0 hm hint (by rw [hmean]; exact hpos) k c X
  simp only [hmean] at hB'
  exact hB'
end YangMills.Construction.TorusLumps
end
