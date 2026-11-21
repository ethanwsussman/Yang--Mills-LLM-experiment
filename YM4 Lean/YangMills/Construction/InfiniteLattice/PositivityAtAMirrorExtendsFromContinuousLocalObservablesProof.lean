import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasures
import YangMills.Construction.InfiniteLattice.PositivityAtAMirrorExtendsFromContinuousLocalObservables
import YangMills.Construction.InfiniteLattice.ReflectionsOfOneFamily
import Mathlib
set_option autoImplicit false
open MeasureTheory Filter
open scoped ComplexConjugate ComplexOrder Topology
noncomputable section
namespace YangMills.Construction.InfiniteLattice
open NormalFamilies
namespace ReflectionPositivityExtension
def l2NormSq (ν : Measure (GaugeField 1)) (H : GaugeField 1 → ℂ) : ℝ :=
  ∫ U, ‖H U‖ ^ 2 ∂ν
variable {ν : Measure (GaugeField 1)} [IsProbabilityMeasure ν]
theorem integrable_of_isBoundedObservable {H : GaugeField 1 → ℂ} (hH : IsBoundedObservable H) :
    Integrable H ν := by
  obtain ⟨hmeas, C, hC⟩ := hH
  exact Integrable.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ hC)
theorem isBoundedObservable_mul {A B : GaugeField 1 → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable (A * B) := by
  obtain ⟨hmA, C, hC⟩ := hA
  obtain ⟨hmB, D, hD⟩ := hB
  refine ⟨hmA.mul hmB, C * D, fun U => ?_⟩
  rw [Pi.mul_apply, norm_mul]
  exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
theorem isBoundedObservable_sub {A B : GaugeField 1 → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable (A - B) := by
  obtain ⟨hmA, C, hC⟩ := hA
  obtain ⟨hmB, D, hD⟩ := hB
  refine ⟨hmA.sub hmB, C + D, fun U => ?_⟩
  rw [Pi.sub_apply]
  exact (norm_sub_le _ _).trans (add_le_add (hC U) (hD U))
theorem integrable_norm_sq {H : GaugeField 1 → ℂ} (hH : IsBoundedObservable H) :
    Integrable (fun U => ‖H U‖ ^ 2) ν := by
  obtain ⟨hmeas, C, hC⟩ := hH
  refine Integrable.of_bound (hmeas.norm.pow_const 2).aestronglyMeasurable (C ^ 2)
    (ae_of_all _ fun U => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
theorem norm_integral_mul_le_sqrt {A B : GaugeField 1 → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) :
    ‖∫ U, (A * B) U ∂ν‖ ≤ Real.sqrt (l2NormSq ν A) * Real.sqrt (l2NormSq ν B) := by
  have memLp : ∀ {H : GaugeField 1 → ℂ}, IsBoundedObservable H →
      MemLp H (ENNReal.ofReal 2) ν := by
    rintro H ⟨hmeas, C, hC⟩
    exact MemLp.of_bound hmeas.aestronglyMeasurable C (ae_of_all _ hC)
  calc ‖∫ U, (A * B) U ∂ν‖ ≤ ∫ U, ‖(A * B) U‖ ∂ν := norm_integral_le_integral_norm _
    _ = ∫ U, ‖A U‖ * ‖B U‖ ∂ν := by simp only [Pi.mul_apply, norm_mul]
    _ ≤ (∫ U, ‖A U‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) * (∫ U, ‖B U‖ ^ (2 : ℝ) ∂ν) ^ (1 / (2 : ℝ)) :=
        integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two (memLp hA) (memLp hB)
    _ = Real.sqrt (l2NormSq ν A) * Real.sqrt (l2NormSq ν B) := by
        simp only [l2NormSq, Real.sqrt_eq_rpow, Real.rpow_two, one_div]
omit [IsProbabilityMeasure ν] in
theorem l2NormSq_conjReflectObservable (P : NormalLevelPair 1)
    (hsymm : IsSymmetricUnder ν P.reflectSymmetry) {H : GaugeField 1 → ℂ}
    (hH : IsBoundedObservable H) : l2NormSq ν (P.conjReflectObservable H) = l2NormSq ν H := by
  have hbdd : IsBoundedObservable (fun U => ((‖H U‖ ^ 2 : ℝ) : ℂ)) := by
    obtain ⟨hmeas, C, hC⟩ := hH
    refine ⟨Complex.measurable_ofReal.comp (hmeas.norm.pow_const 2), C ^ 2, fun U => ?_⟩
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC U) 2
  have h := hsymm _ hbdd
  simp only [LatticeSymmetry.actOn, integral_complex_ofReal] at h
  have h' := Complex.ofReal_injective h
  simpa [l2NormSq, NormalLevelPair.conjReflectObservable, NormalLevelPair.reflectObservable,
    LatticeSymmetry.actOn, RCLike.norm_conj] using h'
theorem l2NormSq_le_two_mul_add {F G : GaugeField 1 → ℂ} (hF : IsBoundedObservable F)
    (hG : IsBoundedObservable G) :
    l2NormSq ν G ≤ 2 * l2NormSq ν F + 2 * l2NormSq ν (F - G) := by
  have hdiff := isBoundedObservable_sub hF hG
  have hsum : 2 * l2NormSq ν F + 2 * l2NormSq ν (F - G) =
      ∫ U, (2 * ‖F U‖ ^ 2 + 2 * ‖(F - G) U‖ ^ 2) ∂ν := by
    rw [integral_add ((integrable_norm_sq hF).const_mul 2)
      ((integrable_norm_sq hdiff).const_mul 2), integral_const_mul, integral_const_mul]
    rfl
  rw [hsum]
  refine integral_mono (integrable_norm_sq hG)
    (((integrable_norm_sq hF).const_mul 2).add ((integrable_norm_sq hdiff).const_mul 2))
    fun U => ?_
  have htri : ‖G U‖ ≤ ‖F U‖ + ‖(F - G) U‖ := by
    have : G U = F U - (F - G) U := by simp
    rw [this]
    exact norm_sub_le _ _
  have h0 := norm_nonneg (G U)
  show ‖G U‖ ^ 2 ≤ 2 * ‖F U‖ ^ 2 + 2 * ‖(F - G) U‖ ^ 2
  nlinarith [sq_nonneg (‖F U‖ - ‖(F - G) U‖), mul_self_le_mul_self h0 htri]
theorem norm_reflectForm_sub_le (P : NormalLevelPair 1)
    (hsymm : IsSymmetricUnder ν P.reflectSymmetry)
    (hrefl : ∀ H : GaugeField 1 → ℂ, IsBoundedObservable H →
      IsBoundedObservable (P.conjReflectObservable H))
    {F G : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) (hG : IsBoundedObservable G) :
    ‖stateEval ν (P.conjReflectObservable F * F) -
        stateEval ν (P.conjReflectObservable G * G)‖ ≤
      Real.sqrt (l2NormSq ν (F - G)) *
        (Real.sqrt (l2NormSq ν F) +
          Real.sqrt (2 * l2NormSq ν F + 2 * l2NormSq ν (F - G))) := by
  have hdiff := isBoundedObservable_sub hF hG
  have hsplit : P.conjReflectObservable F * F - P.conjReflectObservable G * G =
      P.conjReflectObservable (F - G) * F + P.conjReflectObservable G * (F - G) := by
    funext U
    simp only [Pi.sub_apply, Pi.mul_apply, Pi.add_apply, NormalLevelPair.conjReflectObservable,
      NormalLevelPair.reflectObservable, LatticeSymmetry.actOn, map_sub]
    ring
  have hI1 := integrable_of_isBoundedObservable (ν := ν) (isBoundedObservable_mul (hrefl F hF) hF)
  have hI2 := integrable_of_isBoundedObservable (ν := ν) (isBoundedObservable_mul (hrefl G hG) hG)
  have hI3 := integrable_of_isBoundedObservable (ν := ν)
    (isBoundedObservable_mul (hrefl _ hdiff) hF)
  have hI4 := integrable_of_isBoundedObservable (ν := ν)
    (isBoundedObservable_mul (hrefl G hG) hdiff)
  have hexpand : stateEval ν (P.conjReflectObservable F * F) -
        stateEval ν (P.conjReflectObservable G * G) =
      (∫ U, (P.conjReflectObservable (F - G) * F) U ∂ν) +
        ∫ U, (P.conjReflectObservable G * (F - G)) U ∂ν := by
    rw [stateEval, stateEval, ← integral_sub hI1 hI2, ← integral_add hI3 hI4]
    exact integral_congr_ae (ae_of_all _ fun U => congrFun hsplit U)
  rw [hexpand]
  have hb1 := norm_integral_mul_le_sqrt (ν := ν) (hrefl _ hdiff) hF
  have hb2 := norm_integral_mul_le_sqrt (ν := ν) (hrefl G hG) hdiff
  rw [l2NormSq_conjReflectObservable P hsymm hdiff] at hb1
  rw [l2NormSq_conjReflectObservable P hsymm hG] at hb2
  have hb3 : Real.sqrt (l2NormSq ν G) ≤
      Real.sqrt (2 * l2NormSq ν F + 2 * l2NormSq ν (F - G)) :=
    Real.sqrt_le_sqrt (l2NormSq_le_two_mul_add hF hG)
  calc _ ≤ _ := norm_add_le _ _
    _ ≤ Real.sqrt (l2NormSq ν (F - G)) * Real.sqrt (l2NormSq ν F) +
          Real.sqrt (l2NormSq ν G) * Real.sqrt (l2NormSq ν (F - G)) := add_le_add hb1 hb2
    _ ≤ Real.sqrt (l2NormSq ν (F - G)) * Real.sqrt (l2NormSq ν F) +
          Real.sqrt (2 * l2NormSq ν F + 2 * l2NormSq ν (F - G)) *
            Real.sqrt (l2NormSq ν (F - G)) := by gcongr
    _ = _ := by ring
theorem reflectForm_nonneg_of_halfSpace (hdense : ContinuousLocalDensity.Statement)
    (P : NormalLevelPair 1) (hsymm : IsSymmetricUnder ν P.reflectSymmetry)
    (hrefl : ∀ H : GaugeField 1 → ℂ, IsBoundedObservable H →
      IsBoundedObservable (P.conjReflectObservable H))
    (hpos : ∀ F ∈ halfSpaceContinuousLocal 1 P.normal P.level 1,
      0 ≤ stateEval ν (P.conjReflectObservable F * F))
    {F : GaugeField 1 → ℂ} (hF : F ∈ halfSpaceObservables 1 P.normal P.level 1) :
    0 ≤ stateEval ν (P.conjReflectObservable F * F) := by
  obtain ⟨G, hG, hlim⟩ := (hdense ν).1 _ F hF
  have hFb : IsBoundedObservable F := hF.1
  have hGb : ∀ k, 1 ≤ k → IsBoundedObservable (G k) := fun k hk => (hG k hk).1.1
  have herr : Tendsto (fun k => l2NormSq ν (F - G k)) atTop (𝓝 0) := by
    refine hlim.congr fun k => ?_
    simp only [stateEval, l2NormSq, Pi.sub_apply, norm_sub_rev]
  have hcont : Continuous fun x : ℝ => Real.sqrt x *
      (Real.sqrt (l2NormSq ν F) + Real.sqrt (2 * l2NormSq ν F + 2 * x)) := by
    fun_prop
  have hbound : Tendsto (fun k => Real.sqrt (l2NormSq ν (F - G k)) *
      (Real.sqrt (l2NormSq ν F) +
        Real.sqrt (2 * l2NormSq ν F + 2 * l2NormSq ν (F - G k)))) atTop (𝓝 0) := by
    have h := (hcont.tendsto 0).comp herr
    simpa [Function.comp_def] using h
  have hconv : Tendsto (fun k => stateEval ν (P.conjReflectObservable (G k) * G k)) atTop
      (𝓝 (stateEval ν (P.conjReflectObservable F * F))) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hbound
    filter_upwards [eventually_ge_atTop 1] with k hk
    rw [norm_sub_rev]
    exact norm_reflectForm_sub_le P hsymm hrefl hFb (hGb k hk)
  refine ge_of_tendsto hconv ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  exact hpos _ (hG k hk)
end ReflectionPositivityExtension
open ReflectionPositivityExtension in
theorem reflectionPositivityExtendsFromLocal_holds
    (hdense : ContinuousLocalDensity.Statement)
    (hident : ReflectionIdentities.Statement) :
    ReflectionPositivityExtendsFromLocal := by
  intro P ν hν hsymm hpos F hF
  have hfacts := hident P.normal P.normal_mem P.level P.level P.allowed P.allowed 0
  obtain ⟨-, -, -, -, -, -, -, hrefl, -, -, -, -, -, hlower⟩ := hfacts
  rcases hF with hF | hF
  · exact reflectForm_nonneg_of_halfSpace hdense P hsymm hrefl hpos hF
  · obtain ⟨hF', heq⟩ := hlower F hF
    have h := reflectForm_nonneg_of_halfSpace hdense P hsymm hrefl hpos hF'
    have heq' : P.conjReflectObservable F * F =
        P.conjReflectObservable (P.conjReflectObservable F) * P.conjReflectObservable F := by
      rw [mul_comm (P.conjReflectObservable (P.conjReflectObservable F))]
      exact heq
    rw [heq']
    exact h
end YangMills.Construction.InfiniteLattice
