import YangMills.Construction.InfiniteLattice.EquilibriumEquationsAndTheDilationProof
import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.SitesLinksAndPlaquettesOfTheLatticeProof
import YangMills.Construction.ReflectionPositivity.FunctionsOfTheBondsInASet
import Mathlib
set_option autoImplicit false
open Filter Set MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.RegionFunctions
open InfiniteLattice (AmbientSpace GaugeField Link IsLocalObservable IsBoundedObservable
  IsRegionMeasurable regionObservables regionSigma linksWithin positiveLinkSet
  positiveLinksWithin latticeSubgroup trivialField mem_positiveLinks_or_opposite_mem)
open GibbsAtFixedSpacing (BorelProb continuousFns)
open LatticeAtSpacing (RegionLinkVariables restrictToRegion extendFromRegion
  extendFromRegion_of_mem extendFromRegion_of_notMem extendFromRegion_opposite
  borelSpace_regionLinkVariables subsingleton_regionLinkVariables)
variable {a : ℝ}
theorem mem_linksWithin_iff {S : Set AmbientSpace} {b : Link a} :
    b ∈ (linksWithin S : Set (Link a)) ↔
      (b.initial : AmbientSpace) ∈ S ∧ (b.terminal : AmbientSpace) ∈ S :=
  Iff.rfl
theorem mem_positiveLinksWithin_iff {S : Set AmbientSpace} {b : Link a} :
    b ∈ positiveLinksWithin a S ↔ b ∈ positiveLinkSet a ∧ b ∈ (linksWithin S : Set (Link a)) :=
  Iff.rfl
theorem mem_positiveLinksWithin_inter {S T : Set AmbientSpace} {b : Link a} :
    b ∈ positiveLinksWithin a (S ∩ T) ↔
      b ∈ positiveLinksWithin a S ∧ b ∈ positiveLinksWithin a T := by
  simp only [mem_positiveLinksWithin_iff, mem_linksWithin_iff, mem_inter_iff]
  tauto
theorem gaugeField_ext {U V : GaugeField a}
    (h : ∀ b ∈ positiveLinkSet a, U b = V b) : U = V := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsEquations.gaugeField_ext <;> assumption
def keepLinksWithin (ha : 0 < a) (S : Set AmbientSpace) (U : GaugeField a) : GaugeField a :=
  extendFromRegion ha S (restrictToRegion S U)
theorem keepLinksWithin_of_mem (ha : 0 < a) (S : Set AmbientSpace) (U : GaugeField a)
    {b : Link a} (hb : b ∈ positiveLinksWithin a S) : keepLinksWithin ha S U b = U b :=
  extendFromRegion_of_mem ha S (restrictToRegion S U) ⟨b, hb⟩
theorem keepLinksWithin_of_notMem (ha : 0 < a) (S : Set AmbientSpace) (U : GaugeField a)
    {b : Link a} (hp : b ∈ positiveLinkSet a) (hb : b ∉ positiveLinksWithin a S) :
    keepLinksWithin ha S U b = 1 :=
  extendFromRegion_of_notMem ha S (restrictToRegion S U) ⟨hp, hb⟩
theorem keepLinksWithin_of_mem_linksWithin (ha : 0 < a) (S : Set AmbientSpace)
    (U : GaugeField a) {b : Link a} (hb : b ∈ (linksWithin S : Set (Link a))) :
    keepLinksWithin ha S U b = U b := by
  rcases mem_positiveLinks_or_opposite_mem b with hp | hp
  · exact keepLinksWithin_of_mem ha S U (mem_positiveLinksWithin_iff.2 ⟨hp, hb⟩)
  · have hr : b.opposite ∈ positiveLinksWithin a S :=
      mem_positiveLinksWithin_iff.2
        ⟨hp, mem_linksWithin_iff.2 ⟨(mem_linksWithin_iff.1 hb).2, (mem_linksWithin_iff.1 hb).1⟩⟩
    have h₁ := extendFromRegion_opposite ha S (restrictToRegion S U) b.opposite
    have h₂ := U.2 b.opposite
    rw [Link.opposite_opposite] at h₁ h₂
    change keepLinksWithin ha S U b = (keepLinksWithin ha S U b.opposite)⁻¹ at h₁
    rw [h₁, keepLinksWithin_of_mem ha S U hr, ← h₂]
@[reducible] def invariantSets {X : Type*} (e : X → X) : MeasurableSpace X where
  MeasurableSet' s := e ⁻¹' s = s
  measurableSet_empty := rfl
  measurableSet_compl s h := by
    rw [preimage_compl]
    exact congrArg _ h
  measurableSet_iUnion f h := by
    rw [preimage_iUnion]
    exact iUnion_congr h
theorem apply_keepLinksWithin (ha : 0 < a) {S : Set AmbientSpace} {F : GaugeField a → ℂ}
    (hF : IsRegionMeasurable S F) (U : GaugeField a) : F (keepLinksWithin ha S U) = F U := by
  have hle : (regionSigma S : MeasurableSpace (GaugeField a)) ≤
      invariantSets (keepLinksWithin ha S) := by
    refine iSup₂_le fun b hb => ?_
    rintro _ ⟨t, -, rfl⟩
    change keepLinksWithin ha S ⁻¹' ((fun U : GaugeField a => U b) ⁻¹' t) = _
    ext W
    simp only [mem_preimage, keepLinksWithin_of_mem_linksWithin ha S W hb]
  have hs : MeasurableSet[regionSigma S] (F ⁻¹' {F U}) := hF (measurableSet_singleton (F U))
  have hfix : keepLinksWithin ha S ⁻¹' (F ⁻¹' {F U}) = F ⁻¹' {F U} := hle _ hs
  exact show U ∈ keepLinksWithin ha S ⁻¹' (F ⁻¹' {F U}) from by
    rw [hfix]
    exact rfl
theorem continuous_restrictToRegion (S : Set AmbientSpace) :
    Continuous (restrictToRegion S : GaugeField a → RegionLinkVariables a S) :=
  continuous_pi fun b => (continuous_apply b.1).comp continuous_subtype_val
theorem continuous_extendFromRegion_apply_of_positive (ha : 0 < a) (S : Set AmbientSpace)
    {b : Link a} (hp : b ∈ positiveLinkSet a) :
    Continuous fun V : RegionLinkVariables a S => (extendFromRegion ha S V b) := by
  by_cases hb : b ∈ positiveLinksWithin a S
  · have : (fun V : RegionLinkVariables a S => extendFromRegion ha S V b) = fun V => V ⟨b, hb⟩ :=
      funext fun V => extendFromRegion_of_mem ha S V ⟨b, hb⟩
    rw [this]
    exact continuous_apply _
  · have : (fun V : RegionLinkVariables a S => extendFromRegion ha S V b) = fun _ => 1 :=
      funext fun V => extendFromRegion_of_notMem ha S V ⟨hp, hb⟩
    rw [this]
    exact continuous_const
theorem continuous_extendFromRegion (ha : 0 < a) (S : Set AmbientSpace) :
    Continuous (extendFromRegion ha S) := by
  have h : ∀ b : Link a,
      Continuous fun V : RegionLinkVariables a S => extendFromRegion ha S V b := by
    intro b
    rcases mem_positiveLinks_or_opposite_mem b with hp | hp
    · exact continuous_extendFromRegion_apply_of_positive ha S hp
    · have : (fun V : RegionLinkVariables a S => extendFromRegion ha S V b) =
          fun V => (extendFromRegion ha S V b.opposite)⁻¹ :=
        funext fun V => extendFromRegion_opposite ha S V b.opposite
      rw [this]
      exact (continuous_extendFromRegion_apply_of_positive ha S hp).inv
  exact continuous_induced_rng.2 (continuous_pi h)
theorem measurable_restrictToRegion_regionSigma (S : Set AmbientSpace) :
    Measurable[regionSigma S] (restrictToRegion S : GaugeField a → RegionLinkVariables a S) := by
  refine @measurable_pi_lambda _ _ _ (regionSigma S) _ _ fun b => ?_
  exact Measurable.of_comap_le (le_iSup₂_of_le b.1 (mem_positiveLinksWithin_iff.1 b.2).2 le_rfl)
theorem regionObservablesFactor_holds (ha : 0 < a) (S : Set AmbientSpace)
    [CompactSpace (GaugeField a)] [TopologicalSpace.MetrizableSpace (GaugeField a)] :
    RegionObservablesFactor ha S := by
  have hres := continuous_restrictToRegion (a := a) S
  have hext := continuous_extendFromRegion ha S
  have hid : (restrictToRegion S : GaugeField a → RegionLinkVariables a S) ∘
      extendFromRegion ha S = id :=
    funext fun V => funext fun b => extendFromRegion_of_mem ha S V b
  have hinv : Function.LeftInverse (restrictToRegion S : GaugeField a → RegionLinkVariables a S)
      (extendFromRegion ha S) := fun V => congrFun hid V
  have hbs := borelSpace_regionLinkVariables a S
  have hextm : Measurable (extendFromRegion ha S) := hext.measurable
  have hresm : Measurable (restrictToRegion S : GaugeField a → RegionLinkVariables a S) :=
    hres.measurable
  have hcomp : ∀ F ∈ regionObservables a S,
      F = F ∘ extendFromRegion ha S ∘ restrictToRegion S := fun F hF =>
    funext fun U => (apply_keepLinksWithin ha hF.2 U).symm
  have hout : ∀ f : RegionLinkVariables a S → ℂ, IsBddBorel f →
      f ∘ restrictToRegion S ∈ regionObservables a S := by
    rintro f ⟨hf, C, hC⟩
    exact ⟨⟨hf.comp hresm, C, fun U => hC _⟩,
      hf.comp (measurable_restrictToRegion_regionSigma S)⟩
  refine ⟨hres, hext, hid, hinv.surjective.compactSpace hres, ?_, ?_, ?_, ?_⟩
  · exact (hinv.isEmbedding hres hext).metrizableSpace
  · intro F hF
    refine ⟨hcomp F, fun h => ?_⟩
    obtain ⟨hm, C, hC⟩ := hF
    rw [h]
    exact hout _ ⟨hm.comp hextm, C, fun V => hC _⟩
  · intro F hF
    obtain ⟨⟨hm, C, hC⟩, -⟩ := id hF
    exact ⟨⟨hm.comp hextm, C, fun V => hC _⟩, hcomp F hF, fun h => h.comp hext⟩
  · intro f hf
    exact ⟨hout f hf, fun h => h.comp hres⟩
theorem regionSigma_le_of_subset {S T : Set AmbientSpace}
    (h : S ∩ (latticeSubgroup a : Set AmbientSpace) ⊆ T) :
    (regionSigma S : MeasurableSpace (GaugeField a)) ≤ regionSigma T := by
  refine iSup₂_le fun b hb => le_iSup₂_of_le b ?_ le_rfl
  exact mem_linksWithin_iff.2 ⟨h ⟨(mem_linksWithin_iff.1 hb).1, b.initial.2⟩,
    h ⟨(mem_linksWithin_iff.1 hb).2, b.terminal.2⟩⟩
theorem regionObservables_mono {S T : Set AmbientSpace}
    (h : S ∩ (latticeSubgroup a : Set AmbientSpace) ⊆ T) :
    regionObservables a S ⊆ regionObservables a T := fun _ hF =>
  ⟨hF.1, Measurable.mono hF.2 (regionSigma_le_of_subset h) le_rfl⟩
theorem keepLinksWithin_comp (ha : 0 < a) (S T : Set AmbientSpace) (U : GaugeField a) :
    keepLinksWithin ha T (keepLinksWithin ha S U) = keepLinksWithin ha (S ∩ T) U := by
  refine gaugeField_ext fun b hp => ?_
  by_cases hT : b ∈ positiveLinksWithin a T
  · rw [keepLinksWithin_of_mem ha T _ hT]
    by_cases hS : b ∈ positiveLinksWithin a S
    · rw [keepLinksWithin_of_mem ha S _ hS,
        keepLinksWithin_of_mem ha _ _ (mem_positiveLinksWithin_inter.2 ⟨hS, hT⟩)]
    · rw [keepLinksWithin_of_notMem ha S _ hp hS,
        keepLinksWithin_of_notMem ha _ _ hp fun hi => hS (mem_positiveLinksWithin_inter.1 hi).1]
  · rw [keepLinksWithin_of_notMem ha T _ hp hT,
      keepLinksWithin_of_notMem ha _ _ hp fun hi => hT (mem_positiveLinksWithin_inter.1 hi).2]
theorem regionObservables_inter (ha : 0 < a) (S T : Set AmbientSpace)
    [CompactSpace (GaugeField a)] [TopologicalSpace.MetrizableSpace (GaugeField a)] :
    regionObservables a S ∩ regionObservables a T = regionObservables a (S ∩ T) := by
  refine Subset.antisymm (fun F hF => ?_) fun F hF =>
    ⟨regionObservables_mono (fun x hx => hx.1.1) hF,
      regionObservables_mono (fun x hx => hx.1.2) hF⟩
  obtain ⟨-, -, -, -, -, hiff, -, -⟩ := regionObservablesFactor_holds ha (S ∩ T)
  refine (hiff F hF.1.1).2 (funext fun U => ?_)
  change F U = F (keepLinksWithin ha (S ∩ T) U)
  rw [← keepLinksWithin_comp, apply_keepLinksWithin ha hF.2.2, apply_keepLinksWithin ha hF.1.2]
theorem regionObservablesMonotoneInter_holds (ha : 0 < a) (S T : Set AmbientSpace)
    [CompactSpace (GaugeField a)] [TopologicalSpace.MetrizableSpace (GaugeField a)] :
    RegionObservablesMonotoneInter a S T := by
  refine ⟨regionObservables_mono, regionObservables_inter ha S T, fun F hF => ⟨?_, ?_⟩⟩
  · rintro ⟨hS, Q, hQ, hm⟩
    refine ⟨Q, hQ, ?_⟩
    rw [← regionObservables_inter ha]
    exact ⟨hS, hF, hm⟩
  · rintro ⟨Q, hQ, hm⟩
    rw [← regionObservables_inter ha] at hm
    exact ⟨hm.1, Q, hQ, hm.2.2⟩
theorem finite_positiveLinksWithin (ha : 0 < a) {S : Set AmbientSpace}
    (hS : Bornology.IsBounded S) : (positiveLinksWithin a S).Finite := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeGeometry.finite_positiveLinksWithin <;> assumption
theorem linksOfBoundedOrEmptyRegion_holds (ha : 0 < a) (S : Set AmbientSpace) :
    LinksOfBoundedOrEmptyRegion a S := by
  refine ⟨finite_positiveLinksWithin ha, fun h F hF => ⟨F (trivialField a), fun U => ?_⟩⟩
  have := subsingleton_regionLinkVariables (a := a) h
  rw [← apply_keepLinksWithin ha hF.2 U, ← apply_keepLinksWithin ha hF.2 (trivialField a)]
  exact congrArg (fun V => F (extendFromRegion ha S V)) (Subsingleton.elim _ _)
theorem exists_continuous_tendsto_integral_sq {Y : Type*} [TopologicalSpace Y] [CompactSpace Y]
    [TopologicalSpace.MetrizableSpace Y] [MeasurableSpace Y] [BorelSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] {f : Y → ℂ} (hf : Measurable f) {C : ℝ} (hC : ∀ y, ‖f y‖ ≤ C) :
    ∃ g : ℕ → Y → ℂ, (∀ k, Continuous (g k)) ∧
      Tendsto (fun k => ∫ y, ‖f y - g k y‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  let := TopologicalSpace.metrizableSpaceMetric Y
  have hL : MemLp f 2 μ := MemLp.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC)
  have key : ∀ k : ℕ, ∃ g : Y → ℂ, Continuous g ∧
      ∫ y, ‖f y - g y‖ ^ 2 ∂μ ≤ (1 / ((k : ℝ) + 1)) ^ 2 := by
    intro k
    have hε : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    obtain ⟨g, hg, hgL⟩ := hL.exists_boundedContinuous_eLpNorm_sub_le (μ := μ)
      (ε := ENNReal.ofReal (1 / ((k : ℝ) + 1))) (by norm_num)
      (ENNReal.ofReal_pos.2 hε).ne'
    refine ⟨g, g.continuous, ?_⟩
    have hsub : MemLp (f - ⇑g) 2 μ := hL.sub hgL
    rw [hsub.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hg
    have hi : 0 ≤ ∫ y, ‖(f - ⇑g) y‖ ^ (2 : ℝ≥0∞).toReal ∂μ :=
      integral_nonneg fun y => by positivity
    rw [ENNReal.ofReal_le_ofReal_iff hε.le] at hg
    simp only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at hg hi
    have h2 := Real.rpow_le_rpow (by positivity) hg (by norm_num : (0 : ℝ) ≤ 2)
    rw [← Real.rpow_mul hi] at h2
    simpa using h2
  choose g hg hle using key
  refine ⟨g, hg, squeeze_zero (fun k => integral_nonneg fun y => by positivity) hle ?_⟩
  have h0 : Tendsto (fun k : ℕ => 1 / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa using h0.pow 2
theorem sq_integral_le_integral_sq {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    [IsProbabilityMeasure μ] {h : Y → ℝ} (hm : Measurable h) {C : ℝ} (hC : ∀ y, ‖h y‖ ≤ C) :
    (∫ y, h y ∂μ) ^ 2 ≤ ∫ y, h y ^ 2 ∂μ := by
  have hi : Integrable h μ := Integrable.of_bound hm.aestronglyMeasurable C (ae_of_all _ hC)
  have hi₂ : Integrable (fun y => h y ^ 2) μ := by
    refine Integrable.of_bound (hm.pow_const 2).aestronglyMeasurable (C ^ 2)
      (ae_of_all _ fun y => ?_)
    rw [norm_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) (hC y) 2
  set m := ∫ y, h y ∂μ with hmdef
  have hle : ∫ y, 2 * m * h y ∂μ ≤ ∫ y, (h y ^ 2 + m ^ 2) ∂μ := by
    refine integral_mono (hi.const_mul _) (hi₂.add (integrable_const _)) fun y => ?_
    change 2 * m * h y ≤ h y ^ 2 + m ^ 2
    nlinarith [sq_nonneg (h y - m)]
  rw [integral_const_mul, integral_add hi₂ (integrable_const _), integral_const, ← hmdef] at hle
  simp at hle
  nlinarith
theorem sqMean_eq (ν : BorelProb a) (H : GaugeField a → ℂ) :
    sqMean ν H = ((∫ U, ‖H U‖ ^ 2 ∂ν.1 : ℝ) : ℂ) :=
  integral_ofReal
theorem absMean_eq (ν : BorelProb a) (H : GaugeField a → ℂ) :
    absMean ν H = ((∫ U, ‖H U‖ ∂ν.1 : ℝ) : ℂ) :=
  integral_ofReal
theorem tendsto_ofReal_of_tendsto_zero {x : ℕ → ℝ} (h : Tendsto x atTop (𝓝 0)) :
    Tendsto (fun k => (x k : ℂ)) atTop (𝓝 0) := by
  have h₀ := (Complex.continuous_ofReal.tendsto 0).comp h
  rw [Complex.ofReal_zero] at h₀
  exact h₀
theorem continuousApproximation_holds (ha : 0 < a) (S : Set AmbientSpace)
    [CompactSpace (GaugeField a)] [TopologicalSpace.MetrizableSpace (GaugeField a)] :
    ContinuousApproximation a S := by
  intro ν F hF
  have : IsProbabilityMeasure ν.1 := ν.2
  obtain ⟨hFm, C, hC⟩ := id hF
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨g, hg, hlim⟩ := exists_continuous_tendsto_integral_sq ν.1 hFm hC
    refine ⟨g, hg, ?_⟩
    simp only [sqMean_eq]
    exact tendsto_ofReal_of_tendsto_zero hlim
  · intro Fk hFk hlim
    simp only [sqMean_eq] at hlim
    simp only [absMean_eq]
    refine tendsto_ofReal_of_tendsto_zero ?_
    have hq : Tendsto (fun k => ∫ U, ‖(F - Fk k) U‖ ^ 2 ∂ν.1) atTop (𝓝 0) := by
      simpa [Function.comp_def] using (Complex.continuous_re.tendsto 0).comp hlim
    have hs : Tendsto (fun k => Real.sqrt (∫ U, ‖(F - Fk k) U‖ ^ 2 ∂ν.1)) atTop (𝓝 0) := by
      have h₀ := (Real.continuous_sqrt.tendsto 0).comp hq
      rw [Real.sqrt_zero] at h₀
      exact h₀
    refine squeeze_zero (fun k => integral_nonneg fun U => norm_nonneg _) (fun k => ?_) hs
    have hcont : Continuous (Fk k) := hFk k
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn
    have hm : Measurable fun U => ‖(F - Fk k) U‖ := (hFm.sub hcont.measurable).norm
    have hb : ∀ U, ‖‖(F - Fk k) U‖‖ ≤ C + D := fun U => by
      rw [norm_norm]
      exact (norm_sub_le _ _).trans (add_le_add (hC U) (hD U (mem_univ U)))
    exact Real.le_sqrt_of_sq_le (sq_integral_le_integral_sq ν.1 hm hb)
  · intro hS
    obtain ⟨hres, hext, -, hc, hmet, -, hin, hout⟩ := regionObservablesFactor_holds ha S
    have hbs := borelSpace_regionLinkVariables a S
    have hresm : Measurable (restrictToRegion S : GaugeField a → RegionLinkVariables a S) :=
      hres.measurable
    obtain ⟨⟨hfm, D, hD⟩, hFf, -⟩ := hin F hS
    have : IsProbabilityMeasure (ν.1.map (restrictToRegion S)) :=
      Measure.isProbabilityMeasure_map hresm.aemeasurable
    obtain ⟨g, hg, hlim⟩ := exists_continuous_tendsto_integral_sq
      (ν.1.map (restrictToRegion S)) hfm hD
    refine ⟨fun k => g k ∘ restrictToRegion S, fun k => ⟨(hg k).comp hres, ?_⟩, ?_⟩
    · obtain ⟨E, hE⟩ := isCompact_univ.exists_bound_of_continuousOn (hg k).continuousOn
      exact (hout (g k) ⟨(hg k).measurable, E, fun V => hE V (mem_univ V)⟩).1
    · simp only [sqMean_eq]
      refine tendsto_ofReal_of_tendsto_zero ?_
      refine hlim.congr fun k => ?_
      have hmeas : Measurable fun y : RegionLinkVariables a S =>
          ‖(F ∘ extendFromRegion ha S) y - g k y‖ ^ 2 :=
        ((hfm.sub (hg k).measurable).norm).pow_const 2
      rw [integral_map hresm.aemeasurable hmeas.aestronglyMeasurable]
      refine integral_congr_ae (ae_of_all _ fun U => ?_)
      have hU : (F ∘ extendFromRegion ha S) (restrictToRegion S U) = F U :=
        (congrFun hFf U).symm
      simp only [hU, Pi.sub_apply, Function.comp_apply]
theorem regionFunctionsStatement_holds (h : LatticeAtSpacing.LatticeFrameAtSpacing) :
    RegionFunctionsStatement := by
  intro a ha S T
  obtain ⟨hc, hm, -⟩ := (h a ha).1
  exact ⟨regionObservablesFactor_holds ha S, regionObservablesMonotoneInter_holds ha S T,
    linksOfBoundedOrEmptyRegion_holds ha S, continuousApproximation_holds ha S⟩
end YangMills.Construction.ReflectionPositivity.RegionFunctions
