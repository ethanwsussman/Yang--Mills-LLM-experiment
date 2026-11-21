import YangMills.Construction.InfiniteLattice.PlateauVarianceIsTheVarianceOfTheInvariantExpectation
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexOrder ComplexConjugate
noncomputable section
namespace YangMills.Construction.InfiniteLattice
namespace PlateauVariance
theorem integral_norm_sub_integral_sq_eq {Ω : Type*} {m : MeasurableSpace Ω} {μ : Measure Ω}
    [IsProbabilityMeasure μ] {Y : Ω → ℂ} (hY : MemLp Y 2 μ) {c : ℂ}
    (hc : ∫ ω, Y ω ∂μ = c) :
    ((∫ ω, ‖Y ω - c‖ ^ 2 ∂μ : ℝ) : ℂ) =
      (∫ ω, conj (Y ω) * Y ω ∂μ) - ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  have hYi : Integrable Y μ := hY.integrable (by norm_num)
  have hconj : Integrable (fun ω => conj (Y ω)) μ :=
    Complex.conjCLE.toContinuousLinearMap.integrable_comp hYi
  have hsq : Integrable (fun ω => conj (Y ω) * Y ω) μ := by
    have hn : Integrable (fun ω => ‖Y ω‖ ^ 2) μ := hY.integrable_norm_pow (by norm_num)
    refine (hn.ofReal (𝕜 := ℂ)).congr (Filter.Eventually.of_forall fun ω => ?_)
    simp [Complex.conj_mul']
  have hpt : ∀ ω, ((‖Y ω - c‖ ^ 2 : ℝ) : ℂ) =
      conj (Y ω) * Y ω - conj c * Y ω - c * conj (Y ω) + ((‖c‖ ^ 2 : ℝ) : ℂ) := by
    intro ω
    have k₁ := Complex.conj_mul' (Y ω - c)
    have k₂ := Complex.conj_mul' c
    push_cast
    rw [← k₁, ← k₂, map_sub]
    ring
  have hconjInt : ∫ ω, conj (Y ω) ∂μ = conj c := by
    rw [integral_conj, hc]
  rw [← integral_complex_ofReal, integral_congr_ae (Filter.Eventually.of_forall hpt)]
  have j₂ : Integrable (fun ω => conj c * Y ω) μ := hYi.const_mul _
  have j₃ : Integrable (fun ω => c * conj (Y ω)) μ := hconj.const_mul _
  have s₁ := integral_add (μ := μ)
    (f := fun ω => conj (Y ω) * Y ω - conj c * Y ω - c * conj (Y ω))
    (g := fun _ => ((‖c‖ ^ 2 : ℝ) : ℂ)) ((hsq.sub j₂).sub j₃) (integrable_const _)
  have s₂ := integral_sub (μ := μ) (f := fun ω => conj (Y ω) * Y ω - conj c * Y ω)
    (g := fun ω => c * conj (Y ω)) (hsq.sub j₂) j₃
  have s₃ := integral_sub (μ := μ) (f := fun ω => conj (Y ω) * Y ω)
    (g := fun ω => conj c * Y ω) hsq j₂
  rw [s₁, s₂, s₃, integral_const_mul, integral_const_mul, hc, hconjInt, integral_const]
  have k₂ := Complex.conj_mul' c
  simp only [probReal_univ, one_smul]
  push_cast
  rw [← k₂]
  ring
end PlateauVariance
open PlateauVariance in
theorem plateauVarianceFormula_holds : PlateauVarianceFormula := by
  intro a _ μ _ _ F hF
  have hle : shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
    fun S hS => (show IsShiftInvariantSet S from hS).1
  obtain ⟨hFm, B, hB⟩ := hF
  have hF2 : MemLp F 2 μ :=
    MemLp.of_bound hFm.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  have hE2 : MemLp (condExpShiftInvariant μ F) 2 μ := hF2.condExp (by norm_num)
  have hmean : ∫ ω, condExpShiftInvariant μ F ω ∂μ = ∫ ω, F ω ∂μ := integral_condExp hle
  have hvar : plateauVariance μ F =
      ((∫ ω, ‖condExpShiftInvariant μ F ω - ∫ η, F η ∂μ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    rw [integral_norm_sub_integral_sq_eq hE2 hmean]
    rfl
  refine ⟨hmean, hvar, ?_, ?_⟩
  · rw [hmean]
    exact hvar
  · rw [hvar]
    exact Complex.zero_le_real.mpr (integral_nonneg fun ω => by positivity)
end YangMills.Construction.InfiniteLattice
