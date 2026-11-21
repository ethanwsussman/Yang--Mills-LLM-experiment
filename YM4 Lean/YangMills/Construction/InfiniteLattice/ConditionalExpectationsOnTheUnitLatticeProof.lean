import YangMills.Construction.InfiniteLattice.ConditionalExpectationsOnTheUnitLattice
import YangMills.Construction.InfiniteLattice.UnfoldedAndFoldedArraysOfALadder
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate ENNReal
noncomputable section
namespace YangMills.Construction.InfiniteLattice.UnitLatticeCondExp
section General
variable {Ω : Type*} {m m₀ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
theorem integral_bounded_mul_condExp (hm : m ≤ m₀) {J B : Ω → ℂ} (hJ : Measurable[m] J)
    (hbd : ∃ a : ℝ, ∀ U, ‖J U‖ ≤ a) (hB : Integrable B μ) :
    ∫ U, J U * (μ[B | m]) U ∂μ = ∫ U, J U * B U ∂μ := by
  obtain ⟨a, ha⟩ := hbd
  have hJs : StronglyMeasurable[m] J := hJ.stronglyMeasurable
  have hJ0 : AEStronglyMeasurable J μ := (hJs.mono hm).aestronglyMeasurable
  have hJB : Integrable (fun U => J U * B U) μ := by
    refine (hB.norm.const_mul a).mono' (hJ0.mul hB.aestronglyMeasurable) (ae_of_all _ fun U => ?_)
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (ha U) (norm_nonneg _)
  have hpull := condExp_bilin_of_stronglyMeasurable_left (μ := μ) (m := m)
    (ContinuousLinearMap.mul ℝ ℂ) hJs hJB hB
  calc ∫ U, J U * (μ[B | m]) U ∂μ = ∫ U, (μ[fun U => J U * B U | m]) U ∂μ :=
        integral_congr_ae (hpull.symm)
    _ = ∫ U, J U * B U ∂μ := integral_condExp hm
omit [IsProbabilityMeasure μ] in
theorem condExp_complex_linear_comb {B₁ B₂ : Ω → ℂ} (a₁ a₂ : ℂ) (h₁ : Integrable B₁ μ)
    (h₂ : Integrable B₂ μ) :
    μ[fun U => a₁ * B₁ U + a₂ * B₂ U | m] =ᵐ[μ]
      fun U => a₁ * (μ[B₁ | m]) U + a₂ * (μ[B₂ | m]) U := by
  have e : (fun U => a₁ * B₁ U + a₂ * B₂ U) = a₁ • B₁ + a₂ • B₂ := by
    funext U
    simp
  rw [e]
  filter_upwards [condExp_add (h₁.smul a₁) (h₂.smul a₂) m, condExp_smul (μ := μ) a₁ B₁ m,
    condExp_smul (μ := μ) a₂ B₂ m] with U hU hU₁ hU₂
  rw [hU, Pi.add_apply, hU₁, hU₂]
  simp
omit [IsProbabilityMeasure μ] in
theorem condExp_complex_conj {B : Ω → ℂ} (hB : Integrable B μ) :
    μ[fun U => conj (B U) | m] =ᵐ[μ] fun U => conj ((μ[B | m]) U) := by
  have h := (Complex.conjCLE : ℂ →L[ℝ] ℂ).comp_condExp_comm (m := m) hB
  have e : ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ B) = fun U => conj (B U) := by
    funext U
    simp
  rw [e] at h
  filter_upwards [h] with U hU
  rw [← hU]
  simp
def condExpProj (hm : m ≤ m₀) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  (lpMeas ℂ ℂ m 2 μ).subtypeL ∘L condExpL2 ℂ ℂ hm
omit [IsProbabilityMeasure μ] in
theorem condExpProj_eq_starProjection (hm : m ≤ m₀) :
    haveI : Fact (m ≤ m₀) := ⟨hm⟩
    condExpProj (μ := μ) hm = (lpMeas ℂ ℂ m 2 μ).starProjection :=
  rfl
omit [IsProbabilityMeasure μ] in
theorem isStarProjection_condExpProj (hm : m ≤ m₀) :
    IsStarProjection (condExpProj (μ := μ) hm) := by
  have : Fact (m ≤ m₀) := ⟨hm⟩
  rw [condExpProj_eq_starProjection hm]
  exact isStarProjection_starProjection
omit [IsProbabilityMeasure μ] in
theorem range_condExpProj (hm : m ≤ m₀) :
    Set.range (condExpProj (μ := μ) hm) = (lpMeas ℂ ℂ m 2 μ : Set (Lp ℂ 2 μ)) := by
  have : Fact (m ≤ m₀) := ⟨hm⟩
  rw [condExpProj_eq_starProjection hm]
  exact congrArg (fun S : Submodule ℂ (Lp ℂ 2 μ) => (S : Set (Lp ℂ 2 μ)))
    (Submodule.range_starProjection (lpMeas ℂ ℂ m 2 μ))
theorem condExpProj_toLp_ae_eq (hm : m ≤ m₀) {f : Ω → ℂ} (hf : MemLp f 2 μ) :
    (condExpProj hm (hf.toLp f) : Ω → ℂ) =ᵐ[μ] μ[f | m] :=
  hf.condExpL2_ae_eq_condExp (𝕜 := ℂ) hm
theorem condExpProj_ae_eq (hm : m ≤ m₀) (B : Lp ℂ 2 μ) :
    (condExpProj hm B : Ω → ℂ) =ᵐ[μ] μ[(B : Ω → ℂ) | m] := by
  have h := condExpProj_toLp_ae_eq hm (Lp.memLp B)
  rwa [Lp.toLp_coeFn] at h
def aeMeasurableClasses (m : MeasurableSpace Ω) {m₀ : MeasurableSpace Ω} (μ : Measure Ω) :
    Submodule ℂ (Lp ℂ 2 μ) :=
  lpMeas ℂ ℂ m 2 μ
omit [IsProbabilityMeasure μ] in
theorem mem_aeMeasurableClasses_iff (J : Lp ℂ 2 μ) :
    J ∈ aeMeasurableClasses m μ ↔ ∃ g : Ω → ℂ, Measurable[m] g ∧ (J : Ω → ℂ) =ᵐ[μ] g := by
  rw [aeMeasurableClasses, mem_lpMeas_iff_aestronglyMeasurable]
  constructor
  · rintro ⟨g, hg, hJ⟩
    exact ⟨g, hg.measurable, hJ⟩
  · rintro ⟨g, hg, hJ⟩
    exact ⟨g, hg.stronglyMeasurable, hJ⟩
omit [IsProbabilityMeasure μ] in
theorem range_condExpProj_eq_aeMeasurableClasses (hm : m ≤ m₀) :
    Set.range (condExpProj (μ := μ) hm) = (aeMeasurableClasses m μ : Set (Lp ℂ 2 μ)) :=
  range_condExpProj hm
omit [IsProbabilityMeasure μ] in
theorem isClosed_aeMeasurableClasses (hm : m ≤ m₀) :
    IsClosed (aeMeasurableClasses m μ : Set (Lp ℂ 2 μ)) :=
  isClosed_aestronglyMeasurable hm
omit [IsProbabilityMeasure μ] in
theorem integrable_conj_mul_and_integral_eq_inner (F G : Lp ℂ 2 μ) :
    Integrable (fun U => conj (F U) * G U) μ ∧ ∫ U, conj (F U) * G U ∂μ = inner ℂ F G := by
  constructor
  · simpa only [RCLike.inner_apply'] using L2.integrable_inner (𝕜 := ℂ) F G
  · rw [L2.inner_def]
    simp only [RCLike.inner_apply']
omit [IsProbabilityMeasure μ] in
theorem integrable_conj_mul_and_integral_eq_inner_of_ae {f g : Ω → ℂ} {F G : Lp ℂ 2 μ}
    (hf : (F : Ω → ℂ) =ᵐ[μ] f) (hg : (G : Ω → ℂ) =ᵐ[μ] g) :
    Integrable (fun U => conj (f U) * g U) μ ∧ ∫ U, conj (f U) * g U ∂μ = inner ℂ F G := by
  have e : (fun U => conj (F U) * G U) =ᵐ[μ] fun U => conj (f U) * g U := by
    filter_upwards [hf, hg] with U h₁ h₂
    rw [h₁, h₂]
  obtain ⟨h₁, h₂⟩ := integrable_conj_mul_and_integral_eq_inner F G
  exact ⟨h₁.congr e, (integral_congr_ae e).symm.trans h₂⟩
theorem condExp_inner_products (hm : m ≤ m₀) {A B : Ω → ℂ} (hA : MemLp A 2 μ)
    (hB : MemLp B 2 μ) :
    Integrable (fun U => conj ((μ[A | m]) U) * (μ[B | m]) U) μ ∧
    Integrable (fun U => conj (A U) * (μ[B | m]) U) μ ∧
    Integrable (fun U => conj ((μ[A | m]) U) * B U) μ ∧
    ∫ U, conj ((μ[A | m]) U) * (μ[B | m]) U ∂μ = ∫ U, conj (A U) * (μ[B | m]) U ∂μ ∧
    ∫ U, conj (A U) * (μ[B | m]) U ∂μ = ∫ U, conj ((μ[A | m]) U) * B U ∂μ := by
  set a := hA.toLp A
  set b := hB.toLp B
  have ha : (a : Ω → ℂ) =ᵐ[μ] A := hA.coeFn_toLp
  have hb : (b : Ω → ℂ) =ᵐ[μ] B := hB.coeFn_toLp
  have hPa := condExpProj_toLp_ae_eq hm hA
  have hPb := condExpProj_toLp_ae_eq hm hB
  obtain ⟨i₁, e₁⟩ := integrable_conj_mul_and_integral_eq_inner_of_ae hPa hPb
  obtain ⟨i₂, e₂⟩ := integrable_conj_mul_and_integral_eq_inner_of_ae ha hPb
  obtain ⟨i₃, e₃⟩ := integrable_conj_mul_and_integral_eq_inner_of_ae hPa hb
  have hsym : ∀ x y : Lp ℂ 2 μ, inner ℂ (condExpProj hm x) y = inner ℂ x (condExpProj hm y) :=
    fun x y => inner_condExpL2_left_eq_right hm
  have hid : ∀ x : Lp ℂ 2 μ, condExpProj hm (condExpProj hm x) = condExpProj hm x := fun x =>
    congrArg (fun T : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ => T x)
      (isStarProjection_condExpProj (μ := μ) hm).isIdempotentElem
  refine ⟨i₁, i₂, i₃, ?_, ?_⟩
  · rw [e₁, e₂, hsym, hid]
  · rw [e₂, e₃, hsym]
theorem condExp_comp_of_measurePreserving (hm : m ≤ m₀) {φ ψ : Ω → Ω} (hφ : Measurable φ)
    (hmap : μ.map φ = μ) (hφm : @Measurable _ _ m m φ) (hψm : @Measurable _ _ m m ψ)
    (hinv : ∀ x, ψ (φ x) = x) {B : Ω → ℂ} (hB : Integrable B μ) :
    μ[B ∘ φ | m] =ᵐ[μ] (μ[B | m]) ∘ φ := by
  have hmp : MeasurePreserving φ μ μ := ⟨hφ, hmap⟩
  have hBφ : Integrable (B ∘ φ) μ := (hmp.integrable_comp hB.aestronglyMeasurable).mpr hB
  have hEφ : Integrable ((μ[B | m]) ∘ φ) μ :=
    (hmp.integrable_comp integrable_condExp.aestronglyMeasurable).mpr integrable_condExp
  have key : ∀ f : Ω → ℂ, AEStronglyMeasurable f μ → ∀ s, MeasurableSet[m] s →
      ∫ x in s, (f ∘ φ) x ∂μ = ∫ y in ψ ⁻¹' s, f y ∂μ := by
    intro f hf s hs
    have hT : MeasurableSet[m] (ψ ⁻¹' s) := hψm hs
    have hpre : φ ⁻¹' (ψ ⁻¹' s) = s := by
      ext x
      simp [hinv]
    have h := setIntegral_map (μ := μ) (g := φ) (f := f) (hm _ hT) (by rw [hmap]; exact hf)
      hφ.aemeasurable
    rw [hmap, hpre] at h
    exact h.symm
  refine (ae_eq_condExp_of_forall_setIntegral_eq hm hBφ (fun s _ _ => hEφ.integrableOn)
    (fun s hs _ => ?_) ?_).symm
  · rw [key _ integrable_condExp.aestronglyMeasurable s hs, key _ hB.aestronglyMeasurable s hs]
    exact setIntegral_condExp hm hB (hψm hs)
  · exact StronglyMeasurable.aestronglyMeasurable (stronglyMeasurable_condExp.comp_measurable hφm)
end General
theorem indicator_one_mul_eq_indicator (I : Set (GaugeField 1)) (f : GaugeField 1 → ℂ) :
    (fun U => I.indicator (1 : GaugeField 1 → ℂ) U * f U) = I.indicator f := by
  funext U
  by_cases h : U ∈ I <;> simp [h]
theorem isCondExpRepresentative_ae_eq_condExp (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    {𝓕 : MeasurableSpace (GaugeField 1)} (h𝓕 : 𝓕 ≤ borel (GaugeField 1))
    {B E : GaugeField 1 → ℂ} (hB : Integrable B ν)
    (hE : IsCondExpOf ν 𝓕 B E) : E =ᵐ[ν] condExp 𝓕 ν B := by
  obtain ⟨hm, hi, he⟩ := hE
  refine ae_eq_condExp_of_forall_setIntegral_eq h𝓕 hB (fun s _ _ => hi.integrableOn)
    (fun s hs _ => ?_) (StronglyMeasurable.aestronglyMeasurable hm.stronglyMeasurable)
  have h := he s hs
  rw [indicator_one_mul_eq_indicator, indicator_one_mul_eq_indicator,
    integral_indicator (h𝓕 s hs), integral_indicator (h𝓕 s hs)] at h
  exact h
theorem condExpVersionsExist_holds (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (𝓕 : MeasurableSpace (GaugeField 1)) (h𝓕 : 𝓕 ≤ borel (GaugeField 1)) :
    CondExpVersionsExist ν 𝓕 := by
  intro B hB
  refine ⟨⟨_, isCondExpRepresentative_condExpGiven ν h𝓕 hB⟩,
    fun B₁ B₂ h₁ h₂ => (isCondExpRepresentative_ae_eq_condExp ν h𝓕 hB h₁).trans
      (isCondExpRepresentative_ae_eq_condExp ν h𝓕 hB h₂).symm,
    fun B' hB' J hJ hbd => ?_⟩
  rw [← integral_bounded_mul_condExp (μ := ν) h𝓕 hJ hbd hB]
  refine integral_congr_ae ?_
  filter_upwards [isCondExpRepresentative_ae_eq_condExp ν h𝓕 hB hB'] with U hU
  rw [hU]
theorem condExpLinearConjFixes_holds (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (𝓕 : MeasurableSpace (GaugeField 1)) (h𝓕 : 𝓕 ≤ borel (GaugeField 1)) :
    CondExpLinearConjFixes ν 𝓕 := by
  refine ⟨fun a₁ a₂ B₁ B₂ h₁ h₂ => condExp_complex_linear_comb a₁ a₂ h₁ h₂,
    fun B hB => condExp_complex_conj hB, fun B hB hG => ?_⟩
  obtain ⟨G, hG, hBG⟩ := hG
  exact condExp_of_aestronglyMeasurable' h𝓕 ⟨G, hG.stronglyMeasurable, hBG⟩ hB
theorem fieldL2_eq_aeMeasurableClasses (ν : Measure (GaugeField 1))
    (𝓕 : MeasurableSpace (GaugeField 1)) (h𝓕 : 𝓕 ≤ borel (GaugeField 1)) :
    fieldL2 ν 𝓕 h𝓕 = (aeMeasurableClasses 𝓕 ν : Set (Lp ℂ 2 ν)) := by
  ext J
  exact (mem_aeMeasurableClasses_iff J).symm
theorem condExpIsOrthProj_holds (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (𝓕 : MeasurableSpace (GaugeField 1)) (h𝓕 : 𝓕 ≤ borel (GaugeField 1)) :
    CondExpIsOrthProj ν 𝓕 h𝓕 := by
  have hcl := fieldL2_eq_aeMeasurableClasses ν 𝓕 h𝓕
  refine ⟨fun B => ⟨condExpProj h𝓕 B, ?_, condExpProj_ae_eq h𝓕 B⟩,
    ⟨condExpProj h𝓕, ⟨isStarProjection_condExpProj h𝓕, ?_⟩, condExpProj_ae_eq h𝓕⟩,
    ⟨aeMeasurableClasses 𝓕 ν, hcl.symm⟩, ?_,
    fun A B hA hB => condExp_inner_products h𝓕 hA hB⟩
  · rw [hcl]
    exact (range_condExpProj_eq_aeMeasurableClasses h𝓕).subset ⟨B, rfl⟩
  · rw [hcl]
    exact range_condExpProj_eq_aeMeasurableClasses h𝓕
  · rw [hcl]
    exact isClosed_aeMeasurableClasses h𝓕
theorem continuous_pullbackField (r : LatticeSymmetry 1) : Continuous r.pullbackField := by apply _root_.YangMills.Construction.NormalFamilies.continuous_pullbackField <;> assumption
theorem measurable_pullbackField (r : LatticeSymmetry 1) :
    Measurable r.pullbackField :=
  (continuous_pullbackField r).measurable
theorem map_pullbackField_eq (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (r : LatticeSymmetry 1) (hr : IsSymmetricUnder ν r) : ν.map r.pullbackField = ν := by
  have hc := measurable_pullbackField r
  refine Measure.ext fun I hI => ?_
  rw [Measure.map_apply hc hI]
  have hobs : IsBoundedObservable (I.indicator (1 : GaugeField 1 → ℂ)) :=
    ⟨measurable_one.indicator hI, 1, fun U => by
      by_cases h : U ∈ I <;> simp [h]⟩
  have h := hr _ hobs
  have e : r.actOn (I.indicator (1 : GaugeField 1 → ℂ)) =
      (r.pullbackField ⁻¹' I).indicator (fun _ => (1 : ℂ)) := by
    funext U
    by_cases h : r.pullbackField U ∈ I <;> simp [LatticeSymmetry.actOn, h]
  have e' : I.indicator (1 : GaugeField 1 → ℂ) = I.indicator (fun _ => (1 : ℂ)) := rfl
  rw [e, e', integral_indicator_const _ (hc hI), integral_indicator_const _ hI] at h
  have h' : ν.real (r.pullbackField ⁻¹' I) = ν.real I := by
    simpa using h
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp h'
theorem measurable_pullbackField_of_actOn {𝓕 : MeasurableSpace (GaugeField 1)}
    (r : LatticeSymmetry 1)
    (h : ∀ I : Set (GaugeField 1), MeasurableSet[𝓕] I →
      Measurable[𝓕] (r.actOn (I.indicator (1 : GaugeField 1 → ℂ)))) :
    @Measurable _ _ 𝓕 𝓕 r.pullbackField := by
  intro I hI
  have h₁ := h I hI (measurableSet_singleton (1 : ℂ))
  have e : r.actOn (I.indicator (1 : GaugeField 1 → ℂ)) ⁻¹' {1} =
      r.pullbackField ⁻¹' I := by
    ext U
    by_cases h : r.pullbackField U ∈ I <;> simp [LatticeSymmetry.actOn, h]
  rwa [e] at h₁
theorem pullbackField_pullbackField_of_isInverse {r t : LatticeSymmetry 1} (ht : t.IsInverse r)
    (U : GaugeField 1) : t.pullbackField (r.pullbackField U) = U := by
  have hb : ∀ b : Link 1, r.linkMap (t.linkMap b) = b := fun b => by
    apply Link.ext
    · exact Subtype.ext (ht.2 b.initial)
    · exact Subtype.ext (ht.2 b.terminal)
  apply Subtype.ext
  funext b
  change U.1 (r.linkMap (t.linkMap b)) = U.1 b
  rw [hb]
theorem condExpCommutesSymmetry_holds (ν : Measure (GaugeField 1)) [IsProbabilityMeasure ν]
    (𝓕 : MeasurableSpace (GaugeField 1)) (h𝓕 : 𝓕 ≤ borel (GaugeField 1)) :
    CondExpCommutesSymmetry ν 𝓕 := by
  intro r t ht hν hI B hB
  exact condExp_comp_of_measurePreserving h𝓕 (measurable_pullbackField r)
    (map_pullbackField_eq ν r hν)
    (measurable_pullbackField_of_actOn r fun I h => (hI I h).1)
    (measurable_pullbackField_of_actOn t fun I h => (hI I h).2)
    (pullbackField_pullbackField_of_isInverse ht) hB
theorem unitLatticeCondExpProperties_holds : UnitLatticeCondExpProperties := by
  intro ν _ 𝓕 h𝓕
  exact ⟨condExpVersionsExist_holds ν 𝓕 h𝓕, condExpLinearConjFixes_holds ν 𝓕 h𝓕,
    condExpIsOrthProj_holds ν 𝓕 h𝓕, condExpCommutesSymmetry_holds ν 𝓕 h𝓕⟩
end YangMills.Construction.InfiniteLattice.UnitLatticeCondExp
end
