import YangMills.Construction.InfiniteLattice.ReflectionPositivityAndOneTranslationProof
import YangMills.Construction.InfiniteLattice.CoarseStepsAndTheFivePointInequalityProof
import YangMills.Construction.InfiniteLattice.DilationCarriesStatesToSpacingOne
import YangMills.Construction.InfiniteLattice.MovesOfBondsSupportsAndPlaquettes
import YangMills.Construction.InfiniteLattice.ThreeFormsOfTheGibbsPropertyForBondsOfAnyOrientation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate Pointwise
noncomputable section
namespace YangMills.Construction
open InfiniteLattice
open LatticeConventions (NormalHyperplane conjFun euclidDot)
open LatticeConventions.NormalHyperplane (reflectSymmetry)
namespace GibbsAtFixedSpacing.ScalingToUnitSpacing
variable {a : ℝ}
theorem continuous_gaugeFieldUnrescale (ha : 0 < a) :
    Continuous (gaugeFieldUnrescale ha) := by
  refine continuous_induced_rng.2 (continuous_pi fun b => ?_)
  exact (continuous_apply (linkToUnit ha b)).comp continuous_induced_dom
def gaugeFieldHomeomorphUnit (ha : 0 < a) : GaugeField a ≃ₜ GaugeField 1 where
  toEquiv := gaugeFieldEquivUnit ha
  continuous_toFun := continuous_gaugeFieldRescale a
  continuous_invFun := continuous_gaugeFieldUnrescale ha
theorem measurableEmbedding_gaugeFieldRescale (ha : 0 < a) :
    MeasurableEmbedding (gaugeFieldRescale a) :=
  (gaugeFieldHomeomorphUnit ha).toMeasurableEquiv.measurableEmbedding
theorem measurable_gaugeFieldRescale (a : ℝ) : Measurable (gaugeFieldRescale a) :=
  (continuous_gaugeFieldRescale a).measurable
theorem measurable_gaugeFieldUnrescale (ha : 0 < a) :
    Measurable (gaugeFieldUnrescale ha) :=
  (continuous_gaugeFieldUnrescale ha).measurable
theorem unrescale_rescale (ha : 0 < a) (U : GaugeField a) :
    gaugeFieldUnrescale ha (gaugeFieldRescale a U) = U :=
  (gaugeFieldEquivUnit ha).left_inv U
theorem rescale_unrescale (ha : 0 < a) (U : GaugeField 1) :
    gaugeFieldRescale a (gaugeFieldUnrescale ha U) = U :=
  (gaugeFieldEquivUnit ha).right_inv U
theorem gaugeFieldRescale_surjective (ha : 0 < a) : Function.Surjective (gaugeFieldRescale a) :=
  (gaugeFieldEquivUnit ha).surjective
theorem pullToUnit_rescale {E : Type*} (ha : 0 < a) (F : GaugeField a → E)
    (U : GaugeField a) : pullToUnit ha F (gaugeFieldRescale a U) = F U :=
  congrArg F (unrescale_rescale ha U)
theorem pullToUnit_comp_rescale {E : Type*} (ha : 0 < a) (F' : GaugeField 1 → E) :
    pullToUnit ha (F' ∘ gaugeFieldRescale a) = F' :=
  funext fun U => congrArg F' (rescale_unrescale ha U)
theorem pullToUnit_injective {E : Type*} (ha : 0 < a) :
    Function.Injective (pullToUnit (E := E) ha) := by
  intro F G h
  funext U
  rw [← pullToUnit_rescale ha F U, h, pullToUnit_rescale]
theorem image_pullToUnit_eq (ha : 0 < a) {A : Set (GaugeField a → ℂ)}
    {B : Set (GaugeField 1 → ℂ)} (h : ∀ F, pullToUnit ha F ∈ B ↔ F ∈ A) :
    pullToUnit ha '' A = B := by
  ext F'
  constructor
  · rintro ⟨F, hF, rfl⟩
    exact (h F).2 hF
  · intro hF'
    refine ⟨F' ∘ gaugeFieldRescale a, (h _).1 ?_, pullToUnit_comp_rescale ha F'⟩
    rwa [pullToUnit_comp_rescale]
theorem integral_pushToUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ha : 0 < a)
    (ν : Measure (GaugeField a)) (G : GaugeField 1 → E) :
    ∫ U, G U ∂pushToUnit ν = ∫ U, G (gaugeFieldRescale a U) ∂ν :=
  (measurableEmbedding_gaugeFieldRescale ha).integral_map G
theorem integral_pullToUnit {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (ha : 0 < a)
    (ν : Measure (GaugeField a)) (F : GaugeField a → E) :
    ∫ U, pullToUnit ha F U ∂pushToUnit ν = ∫ U, F U ∂ν := by
  rw [integral_pushToUnit ha]
  simp only [pullToUnit_rescale]
theorem BorelProb.integral_toUnit (ha : 0 < a) (ν : BorelProb a) (F : GaugeField a → ℂ) :
    (BorelProb.toUnit ν).integral (pullToUnit ha F) = ν.integral F :=
  ScalingToUnitSpacing.integral_pullToUnit ha ν.1 F
theorem isBoundedObservable_pullToUnit (ha : 0 < a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (pullToUnit ha F) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨hm.comp (measurable_gaugeFieldUnrescale ha), C, fun U => hC _⟩
theorem isBoundedObservable_comp_rescale {F : GaugeField 1 → ℂ} (hF : IsBoundedObservable F) :
    IsBoundedObservable (F ∘ gaugeFieldRescale a) := by
  obtain ⟨hm, C, hC⟩ := hF
  exact ⟨hm.comp (measurable_gaugeFieldRescale a), C, fun U => hC _⟩
theorem supNorm_pullToUnit (ha : 0 < a) (F : GaugeField a → ℂ) :
    observableSupNorm (pullToUnit ha F) = observableSupNorm F :=
  (gaugeFieldEquivUnit ha).symm.surjective.iSup_comp fun U => ‖F U‖
theorem mem_inverseScaling_image_iff (ha : 0 < a) (S : Set AmbientSpace) (x : AmbientSpace) :
    x ∈ inverseScaling ha '' S ↔ a • x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have e : a • inverseScaling ha y = y := (inverseScaling ha).left_inv y
    rwa [e]
  · intro h
    exact ⟨a • x, h, (inverseScaling ha).right_inv x⟩
theorem linkOfUnit_mem_linksWithin_iff (ha : 0 < a) (S : Set AmbientSpace) (b : Link 1) :
    linkOfUnit a b ∈ linksWithin S ↔ b ∈ linksWithin (inverseScaling ha '' S) :=
  and_congr (mem_inverseScaling_image_iff ha S _).symm (mem_inverseScaling_image_iff ha S _).symm
theorem linkOfUnit_linkToUnit (ha : 0 < a) (b : Link a) :
    linkOfUnit a (linkToUnit ha b) = b :=
  (linkEquivUnit ha).right_inv b
theorem comap_regionSigma (ha : 0 < a) (S : Set AmbientSpace) :
    MeasurableSpace.comap (gaugeFieldRescale a) (regionSigma (a := 1) (inverseScaling ha '' S)) =
      regionSigma (a := a) S := by
  apply le_antisymm
  · simp only [regionSigma, linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun b hb => ?_
    exact le_iSup₂_of_le (linkOfUnit a b)
      ((linkOfUnit_mem_linksWithin_iff ha S b).2 hb) le_rfl
  · simp only [regionSigma, linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
    refine iSup₂_le fun b hb => ?_
    have hb' : linkToUnit ha b ∈ linksWithin (a := 1) (inverseScaling ha '' S) := by
      rw [← linkOfUnit_mem_linksWithin_iff ha, linkOfUnit_linkToUnit]
      exact hb
    refine le_iSup₂_of_le (linkToUnit ha b) hb' ?_
    have e : (fun U : GaugeField 1 => U (linkToUnit ha b)) ∘
        gaugeFieldRescale a = fun U : GaugeField a => U b :=
      funext fun U => congrArg U.1 (linkOfUnit_linkToUnit ha b)
    rw [e]
theorem measurable_comap_iff_pullToUnit (ha : 0 < a) (m : MeasurableSpace (GaugeField 1))
    (F : GaugeField a → ℂ) :
    Measurable[MeasurableSpace.comap (gaugeFieldRescale a) m] F ↔
      Measurable[m] (pullToUnit ha F) := by
  constructor
  · intro h s hs
    obtain ⟨t, ht, hts⟩ := h hs
    have e : pullToUnit ha F ⁻¹' s = t := by
      ext U
      have h1 : gaugeFieldUnrescale ha U ∈ gaugeFieldRescale a ⁻¹' t ↔
          gaugeFieldUnrescale ha U ∈ F ⁻¹' s := by rw [hts]
      have h2 : gaugeFieldUnrescale ha U ∈ gaugeFieldRescale a ⁻¹' t ↔
          U ∈ t := by
        rw [mem_preimage, rescale_unrescale]
      exact (h2.symm.trans h1).symm
    rwa [e]
  · intro h
    have e : F = pullToUnit ha F ∘ gaugeFieldRescale a :=
      (funext (pullToUnit_rescale ha F)).symm
    rw [e]
    exact h.comp (comap_measurable _)
theorem pullToUnit_mem_boundedMeasurableIn_iff (ha : 0 < a) (S : Set AmbientSpace)
    (F : GaugeField a → ℂ) :
    pullToUnit ha F ∈ boundedMeasurableIn 1 (inverseScaling ha '' S) ↔
      F ∈ boundedMeasurableIn a S := by
  constructor
  · rintro ⟨hm, C, hC⟩
    refine ⟨?_, C, fun U => ?_⟩
    · rw [← comap_regionSigma ha S]
      exact (measurable_comap_iff_pullToUnit ha _ F).2 hm
    · have := hC (gaugeFieldRescale a U)
      rwa [pullToUnit_rescale] at this
  · rintro ⟨hm, C, hC⟩
    refine ⟨?_, C, fun U => hC _⟩
    rw [← comap_regionSigma ha S] at hm
    exact (measurable_comap_iff_pullToUnit ha _ F).1 hm
theorem isBounded_inverseScaling_image (ha : 0 < a) {Q : Set AmbientSpace}
    (h : Bornology.IsBounded Q) : Bornology.IsBounded (inverseScaling ha '' Q) := by
  have e : inverseScaling ha '' Q = a⁻¹ • Q := rfl
  rw [e]
  exact h.smul₀ _
theorem isBounded_inverseScaling_symm_image (ha : 0 < a) {Q : Set AmbientSpace}
    (h : Bornology.IsBounded Q) : Bornology.IsBounded ((inverseScaling ha).symm '' Q) := by
  have e : (inverseScaling ha).symm '' Q = a • Q := rfl
  rw [e]
  exact h.smul₀ _
theorem pullToUnit_mem_locallyMeasurableIn_iff (ha : 0 < a) (S : Set AmbientSpace)
    (F : GaugeField a → ℂ) :
    pullToUnit ha F ∈ locallyMeasurableIn 1 (inverseScaling ha '' S) ↔
      F ∈ locallyMeasurableIn a S := by
  simp only [locallyMeasurableIn, mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · rintro ⟨Q, hQ, hF⟩
    refine ⟨(inverseScaling ha).symm '' Q, isBounded_inverseScaling_symm_image ha hQ, ?_⟩
    rw [← pullToUnit_mem_boundedMeasurableIn_iff ha, image_inter (inverseScaling ha).injective,
      (inverseScaling ha).image_symm_image]
    exact hF
  · rintro ⟨Q, hQ, hF⟩
    refine ⟨inverseScaling ha '' Q, isBounded_inverseScaling_image ha hQ, ?_⟩
    rw [← image_inter (inverseScaling ha).injective, pullToUnit_mem_boundedMeasurableIn_iff ha]
    exact hF
theorem pullToUnit_mem_continuousFns_iff (ha : 0 < a) (F : GaugeField a → ℂ) :
    pullToUnit ha F ∈ continuousFns 1 ↔ F ∈ continuousFns a := by
  constructor
  · intro h
    have h' : Continuous (pullToUnit ha F ∘ gaugeFieldRescale a) :=
      Continuous.comp h (continuous_gaugeFieldRescale a)
    have e : pullToUnit ha F ∘ gaugeFieldRescale a = F :=
      funext (pullToUnit_rescale ha F)
    rw [e] at h'
    exact h'
  · intro h
    exact Continuous.comp h (continuous_gaugeFieldUnrescale ha)
def BorelProb.fromUnit (ha : 0 < a) (ν : BorelProb 1) : BorelProb a :=
  ⟨ν.1.map (gaugeFieldUnrescale ha), haveI := ν.2;
    Measure.isProbabilityMeasure_map (measurable_gaugeFieldUnrescale ha).aemeasurable⟩
theorem BorelProb.integral_fromUnit (ha : 0 < a) (ν : BorelProb 1) (F : GaugeField a → ℂ) :
    (BorelProb.fromUnit ha ν).integral F = ν.integral (pullToUnit ha F) := by
  have hE : MeasurableEmbedding (gaugeFieldUnrescale ha) :=
    (gaugeFieldHomeomorphUnit ha).symm.toMeasurableEquiv.measurableEmbedding
  exact hE.integral_map F
def borelProbEquivUnit (ha : 0 < a) : BorelProb a ≃ BorelProb 1 where
  toFun := BorelProb.toUnit
  invFun := BorelProb.fromUnit ha
  left_inv ν := by
    refine Subtype.ext ?_
    change (ν.1.map (gaugeFieldRescale a)).map (gaugeFieldUnrescale ha) = ν.1
    rw [Measure.map_map (measurable_gaugeFieldUnrescale ha) (measurable_gaugeFieldRescale a)]
    have e : gaugeFieldUnrescale ha ∘ gaugeFieldRescale a = id :=
      funext (unrescale_rescale ha)
    rw [e, Measure.map_id]
  right_inv ν := by
    refine Subtype.ext ?_
    change (ν.1.map (gaugeFieldUnrescale ha)).map (gaugeFieldRescale a) = ν.1
    rw [Measure.map_map (measurable_gaugeFieldRescale a) (measurable_gaugeFieldUnrescale ha)]
    have e : gaugeFieldRescale a ∘ gaugeFieldUnrescale ha = id :=
      funext (rescale_unrescale ha)
    rw [e, Measure.map_id]
theorem continuous_expectation (F : continuousFns a) :
    Continuous fun ν : BorelProb a => ν.integral F.1 :=
  continuous_iInf_dom
    (t₁ := fun F : continuousFns a =>
      TopologicalSpace.induced (fun ν : BorelProb a => ν.integral F.1) inferInstance)
    (i := F) continuous_induced_dom
theorem continuous_toUnit (ha : 0 < a) : Continuous (BorelProb.toUnit (a := a)) := by
  refine continuous_iInf_rng.2 fun F => continuous_induced_rng.2 ?_
  have hc : F.1 ∘ gaugeFieldRescale a ∈ continuousFns a :=
    Continuous.comp F.2 (continuous_gaugeFieldRescale a)
  have e : ((fun ν : BorelProb 1 => ν.integral F.1) ∘ BorelProb.toUnit (a := a)) =
      fun ν : BorelProb a => ν.integral (F.1 ∘ gaugeFieldRescale a) := by
    funext ν
    exact integral_pushToUnit ha ν.1 F.1
  rw [e]
  exact continuous_expectation ⟨_, hc⟩
theorem continuous_fromUnit (ha : 0 < a) : Continuous (BorelProb.fromUnit ha) := by
  refine continuous_iInf_rng.2 fun F => continuous_induced_rng.2 ?_
  have hc : pullToUnit ha F.1 ∈ continuousFns 1 :=
    (pullToUnit_mem_continuousFns_iff ha F.1).2 F.2
  have e : ((fun ν : BorelProb a => ν.integral F.1) ∘ BorelProb.fromUnit ha) =
      fun ν : BorelProb 1 => ν.integral (pullToUnit ha F.1) := by
    funext ν
    exact BorelProb.integral_fromUnit ha ν F.1
  rw [e]
  exact continuous_expectation ⟨_, hc⟩
theorem transportsFieldsObservablesMeasures (ha : 0 < a) :
    TransportsFieldsObservablesMeasures ha := by
  refine ⟨⟨gaugeFieldHomeomorphUnit ha, rfl⟩, ⟨fun F hF => isBoundedObservable_pullToUnit ha hF,
      (pullToUnit_injective ha).injOn, fun F' hF' => ?_⟩, fun F G _ _ => ⟨rfl, rfl⟩,
      fun c F _ => rfl, fun F _ => ⟨rfl, supNorm_pullToUnit ha F⟩,
      image_pullToUnit_eq ha (pullToUnit_mem_continuousFns_iff ha),
      fun S => ⟨image_pullToUnit_eq ha (pullToUnit_mem_boundedMeasurableIn_iff ha S),
        image_pullToUnit_eq ha (pullToUnit_mem_locallyMeasurableIn_iff ha S)⟩,
      fun ν F _ => BorelProb.integral_toUnit ha ν F,
      ⟨{ toEquiv := borelProbEquivUnit ha, continuous_toFun := continuous_toUnit ha,
         continuous_invFun := continuous_fromUnit ha }, fun _ => rfl, ?_⟩⟩
  · exact ⟨F' ∘ gaugeFieldRescale a, isBoundedObservable_comp_rescale hF',
      pullToUnit_comp_rescale ha F'⟩
  · intro ν ν₁ ν₂ t _ _ h
    change (ν.1).map (gaugeFieldRescale a) = _
    rw [h, Measure.map_add _ _ (measurable_gaugeFieldRescale a), Measure.map_smul, Measure.map_smul]
    rfl
theorem symmetry_ext {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem linkMap_toUnit (ha : 0 < a) (r : LatticeSymmetry a) (b : Link 1) :
    linkOfUnit a ((r.toUnit ha).linkMap b) = r.linkMap (linkOfUnit a b) := by
  apply Link.ext <;> apply Subtype.ext
  · exact smul_inv_smul₀ ha.ne' _
  · exact smul_inv_smul₀ ha.ne' _
theorem rescale_pullbackField (ha : 0 < a) (r : LatticeSymmetry a) (U : GaugeField a) :
    gaugeFieldRescale a (r.pullbackField U) =
      (r.toUnit ha).pullbackField (gaugeFieldRescale a U) := by
  refine Subtype.ext (funext fun b => ?_)
  change U (r.linkMap (linkOfUnit a b)) = U (linkOfUnit a ((r.toUnit ha).linkMap b))
  rw [linkMap_toUnit]
theorem pullToUnit_actOn {E : Type*} (ha : 0 < a) (r : LatticeSymmetry a)
    (F : GaugeField a → E) :
    pullToUnit ha (r.actOn F) = (r.toUnit ha).actOn (pullToUnit ha F) := by
  funext U
  have h := rescale_pullbackField ha r (gaugeFieldUnrescale ha U)
  rw [rescale_unrescale] at h
  change F (r.pullbackField (gaugeFieldUnrescale ha U)) =
    F (gaugeFieldUnrescale ha ((r.toUnit ha).pullbackField U))
  rw [← h, unrescale_rescale]
def symmetryFromUnit (ha : 0 < a) (t : LatticeSymmetry 1) : LatticeSymmetry a where
  toFun := (inverseScaling ha).symm ∘ t.toFun ∘ inverseScaling ha
  preservesDist x y := by
    have hr := t.preservesDist (inverseScaling ha x) (inverseScaling ha y)
    have h₁ : inverseScaling ha x - inverseScaling ha y = a⁻¹ • (x - y) :=
      (smul_sub a⁻¹ x y).symm
    have h₂ : ((inverseScaling ha).symm ∘ t.toFun ∘ inverseScaling ha) x -
        ((inverseScaling ha).symm ∘ t.toFun ∘ inverseScaling ha) y =
        a • (t.toFun (inverseScaling ha x) - t.toFun (inverseScaling ha y)) :=
      (smul_sub a _ _).symm
    rw [h₂, euclidNormVec_smul, hr, h₁, euclidNormVec_smul, abs_inv, abs_of_pos ha,
      mul_inv_cancel_left₀ ha.ne']
  image_eq := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      have h : t.toFun (inverseScaling ha x) ∈
          t.toFun '' (latticeSubgroup 1 : Set AmbientSpace) :=
        ⟨inverseScaling ha x, (pointToUnit ha ⟨x, hx⟩).2, rfl⟩
      rw [t.image_eq] at h
      exact (pointOfUnit a ⟨_, h⟩).2
    · intro hy
      have h : inverseScaling ha y ∈ t.toFun '' (latticeSubgroup 1 : Set AmbientSpace) := by
        rw [t.image_eq]
        exact (pointToUnit ha ⟨y, hy⟩).2
      obtain ⟨z, hz, hzy⟩ := h
      refine ⟨a • z, (pointOfUnit a ⟨z, hz⟩).2, ?_⟩
      change (inverseScaling ha).symm (t.toFun (inverseScaling ha ((inverseScaling ha).symm z))) = y
      rw [Equiv.apply_symm_apply, hzy, Equiv.symm_apply_apply]
theorem conjByScaling_shift (ha : 0 < a) (v : LatticePoint a) :
    conjByScaling ha (shift v).toFun = (shift (pointToUnit ha v)).toFun := by
  funext x
  change a⁻¹ • (a • x + (v : AmbientSpace)) = x + a⁻¹ • (v : AmbientSpace)
  rw [smul_add, inv_smul_smul₀ ha.ne']
theorem toUnit_shift (ha : 0 < a) (v : LatticePoint a) :
    (shift v).toUnit ha = shift (pointToUnit ha v) :=
  symmetry_ext (conjByScaling_shift ha v)
theorem euclidDot_smul (n x : AmbientSpace) (c : ℝ) : euclidDot n (c • x) = c * euclidDot n x := by apply _root_.YangMills.Construction.LatticeConventions.TranslationReflectionProof.euclidDot_smul <;> assumption
theorem isLatticeMirror_iff_of_scaled (ha : 0 < a) {Q Q' : NormalHyperplane}
    (h : IsScaledPair a Q Q') : Q.IsLatticeMirror a ↔ Q'.IsLatticeMirror 1 := by
  obtain ⟨h₁, h₂⟩ := h
  have e₁ : ∀ q : ℤ, Q.level = (q : ℝ) * (a / 2) ↔ Q'.level = (q : ℝ) * (1 / 2) := by
    intro q
    rw [h₂, div_eq_iff ha.ne']
    constructor <;> intro e <;> rw [e] <;> ring
  have e₂ : ∀ q : ℤ, Q.level = (q : ℝ) * a ↔ Q'.level = (q : ℝ) * 1 := by
    intro q
    rw [h₂, div_eq_iff ha.ne']
    constructor <;> intro e <;> rw [e] <;> ring
  unfold NormalHyperplane.IsLatticeMirror
  rw [h₁]
  simp only [e₁, e₂]
theorem inverseScaling_image_carrier (ha : 0 < a) {Q Q' : NormalHyperplane}
    (h : IsScaledPair a Q Q') : inverseScaling ha '' Q.carrier = Q'.carrier := by
  obtain ⟨h₁, h₂⟩ := h
  ext x
  rw [mem_inverseScaling_image_iff]
  change euclidDot Q.normal (a • x) = Q.level ↔ euclidDot Q'.normal x = Q'.level
  rw [euclidDot_smul, h₁, h₂, eq_div_iff ha.ne', mul_comm]
theorem inverseScaling_image_upperHalfSpace (ha : 0 < a) {Q Q' : NormalHyperplane}
    (h : IsScaledPair a Q Q') : inverseScaling ha '' Q.upperHalfSpace = Q'.upperHalfSpace := by
  obtain ⟨h₁, h₂⟩ := h
  ext x
  rw [mem_inverseScaling_image_iff]
  change Q.level ≤ euclidDot Q.normal (a • x) ↔ Q'.level ≤ euclidDot Q'.normal x
  rw [euclidDot_smul, h₁, h₂, div_le_iff₀' ha]
theorem inverseScaling_image_lowerHalfSpace (ha : 0 < a) {Q Q' : NormalHyperplane}
    (h : IsScaledPair a Q Q') : inverseScaling ha '' Q.lowerHalfSpace = Q'.lowerHalfSpace := by
  obtain ⟨h₁, h₂⟩ := h
  ext x
  rw [mem_inverseScaling_image_iff]
  change euclidDot Q.normal (a • x) ≤ Q.level ↔ euclidDot Q'.normal x ≤ Q'.level
  rw [euclidDot_smul, h₁, h₂, le_div_iff₀' ha]
theorem conjByScaling_reflect (ha : 0 < a) {Q Q' : NormalHyperplane}
    (h : IsScaledPair a Q Q') : conjByScaling ha Q.reflect = Q'.reflect := by
  obtain ⟨h₁, h₂⟩ := h
  funext x
  change a⁻¹ • (a • x - (2 * (euclidDot Q.normal (a • x) - Q.level) /
      LatticeConventions.euclidNorm Q.normal ^ 2) • Q.normal) =
    x - (2 * (euclidDot Q'.normal x - Q'.level) /
      LatticeConventions.euclidNorm Q'.normal ^ 2) • Q'.normal
  rw [h₁, h₂, euclidDot_smul, smul_sub, inv_smul_smul₀ ha.ne', smul_smul]
  congr 2
  field_simp
theorem transportsSymmetriesAndMirrors (ha : 0 < a)
    (hMoves : SymmetriesTransportLinksSupportsAndPlaquettes) :
    TransportsSymmetriesAndMirrors ha := by
  refine ⟨fun r => ⟨r.toUnit ha, rfl⟩, fun t => ⟨symmetryFromUnit ha t, ?_⟩,
    fun r F _ => pullToUnit_actOn ha r F, conjByScaling_shift ha, ?_, ?_,
    (hMoves a ha).1.1⟩
  · funext x
    change t.toFun x = inverseScaling ha ((inverseScaling ha).symm
      (t.toFun (inverseScaling ha ((inverseScaling ha).symm x))))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  · intro r hr
    funext x
    change a⁻¹ • r.toFun (a • x) = r.toFun x
    rw [hr.map_smul, inv_smul_smul₀ ha.ne']
  · intro Q Q' h
    exact ⟨isLatticeMirror_iff_of_scaled ha h, inverseScaling_image_carrier ha h,
      inverseScaling_image_upperHalfSpace ha h, inverseScaling_image_lowerHalfSpace ha h,
      conjByScaling_reflect ha h⟩
theorem isSymmetricUnder_toUnit_iff (ha : 0 < a) (ν : Measure (GaugeField a))
    (r : LatticeSymmetry a) :
    IsSymmetricUnder ν r ↔ IsSymmetricUnder (pushToUnit ν) (r.toUnit ha) := by
  constructor
  · intro h A' hA'
    have e := pullToUnit_comp_rescale ha A'
    have h₁ := h (A' ∘ gaugeFieldRescale a) (isBoundedObservable_comp_rescale hA')
    rw [← integral_pullToUnit ha ν (r.actOn _), ← integral_pullToUnit ha ν (A' ∘ _),
      pullToUnit_actOn, e] at h₁
    exact h₁
  · intro h A hA
    have h₁ := h (pullToUnit ha A) (isBoundedObservable_pullToUnit ha hA)
    rw [← pullToUnit_actOn, integral_pullToUnit, integral_pullToUnit] at h₁
    exact h₁
theorem pointToUnit_surjective (ha : 0 < a) :
    Function.Surjective (pointToUnit ha) :=
  fun v => ⟨pointOfUnit a v, pointToUnit_pointOfUnit ha v⟩
theorem isShiftInvariant_pushToUnit_iff (ha : 0 < a) (ν : Measure (GaugeField a)) :
    IsShiftInvariant ν ↔ IsShiftInvariant (pushToUnit ν) := by
  constructor
  · intro h v'
    obtain ⟨v, rfl⟩ := pointToUnit_surjective ha v'
    rw [← toUnit_shift]
    exact (isSymmetricUnder_toUnit_iff ha ν _).1 (h v)
  · intro h v
    refine (isSymmetricUnder_toUnit_iff ha ν _).2 ?_
    rw [toUnit_shift]
    exact h _
theorem reflectedPairing_toUnit (ha : 0 < a) {Q Q' : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (hQ' : Q'.IsLatticeMirror 1) (h : IsScaledPair a Q Q')
    (ν : BorelProb a) (F : GaugeField a → ℂ) :
    reflectedPairing hQ' (BorelProb.toUnit ν) (pullToUnit ha F) = reflectedPairing hQ ν F := by
  have e : (reflectSymmetry hQ).toUnit ha = reflectSymmetry hQ' :=
    symmetry_ext (conjByScaling_reflect ha h)
  unfold reflectedPairing
  rw [← e, ← pullToUnit_actOn]
  exact BorelProb.integral_toUnit ha ν fun U =>
    conjFun ((reflectSymmetry hQ).actOn F) U * F U
theorem isLocallyReflectionPositive_toUnit_iff (ha : 0 < a) {Q Q' : NormalHyperplane}
    (hQ : Q.IsLatticeMirror a) (hQ' : Q'.IsLatticeMirror 1) (h : IsScaledPair a Q Q')
    (ν : BorelProb a) :
    IsLocallyReflectionPositive hQ ν ↔ IsLocallyReflectionPositive hQ' (BorelProb.toUnit ν) := by
  have hmem : ∀ F : GaugeField a → ℂ,
      pullToUnit ha F ∈ locallyMeasurableIn 1 Q'.upperHalfSpace ↔
        F ∈ locallyMeasurableIn a Q.upperHalfSpace := fun F => by
    rw [← inverseScaling_image_upperHalfSpace ha h, pullToUnit_mem_locallyMeasurableIn_iff]
  constructor
  · intro hp F' hF'
    have e := pullToUnit_comp_rescale ha F'
    rw [← e] at hF' ⊢
    rw [reflectedPairing_toUnit ha hQ hQ' h]
    exact hp _ ((hmem _).1 hF')
  · intro hp F hF
    rw [← reflectedPairing_toUnit ha hQ hQ' h]
    exact hp _ ((hmem F).2 hF)
theorem isShiftInvariantSet_preimage_iff (ha : 0 < a) (t : Set (GaugeField 1)) :
    IsShiftInvariantSet (gaugeFieldRescale a ⁻¹' t) ↔ IsShiftInvariantSet t := by
  have hms : MeasurableSet (gaugeFieldRescale a ⁻¹' t) ↔ MeasurableSet t :=
    (gaugeFieldHomeomorphUnit ha).toMeasurableEquiv.measurableSet_preimage
  have hv : ∀ v : LatticePoint a,
      (shift v).pullbackField ⁻¹' (gaugeFieldRescale a ⁻¹' t) =
          gaugeFieldRescale a ⁻¹' t ↔
        (shift (pointToUnit ha v)).pullbackField ⁻¹' t = t := by
    intro v
    have e : (shift v).pullbackField ⁻¹' (gaugeFieldRescale a ⁻¹' t) =
        gaugeFieldRescale a ⁻¹'
          ((shift (pointToUnit ha v)).pullbackField ⁻¹' t) := by
      ext U
      change gaugeFieldRescale a ((shift v).pullbackField U) ∈ t ↔
        (shift (pointToUnit ha v)).pullbackField
          (gaugeFieldRescale a U) ∈ t
      rw [rescale_pullbackField ha, toUnit_shift]
    rw [e]
    exact (gaugeFieldRescale_surjective ha).preimage_injective.eq_iff
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨hms.1 h₁, fun v' => ?_⟩
    obtain ⟨v, rfl⟩ := pointToUnit_surjective ha v'
    rw [LatticeSymmetry.actOn_indicator_eq_iff, ← hv]
    exact ((shift v).actOn_indicator_eq_iff _).1 (h₂ v)
  · rintro ⟨h₁, h₂⟩
    refine ⟨hms.2 h₁, fun v => ?_⟩
    rw [LatticeSymmetry.actOn_indicator_eq_iff, hv]
    exact ((shift _).actOn_indicator_eq_iff _).1 (h₂ _)
theorem preimage_rescale_preimage_unrescale (ha : 0 < a) (s : Set (GaugeField a)) :
    gaugeFieldRescale a ⁻¹' (gaugeFieldUnrescale ha ⁻¹' s) = s := by
  ext U
  change gaugeFieldUnrescale ha (gaugeFieldRescale a U) ∈ s ↔ U ∈ s
  rw [unrescale_rescale]
theorem comap_shiftInvariantSigma (ha : 0 < a) :
    MeasurableSpace.comap (gaugeFieldRescale a) (shiftInvariantSigma 1) =
      shiftInvariantSigma a := by
  ext s
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact (isShiftInvariantSet_preimage_iff ha t).2 ht
  · intro hs
    refine ⟨gaugeFieldUnrescale ha ⁻¹' s, ?_, preimage_rescale_preimage_unrescale ha s⟩
    refine (isShiftInvariantSet_preimage_iff ha _).1 ?_
    rw [preimage_rescale_preimage_unrescale]
    exact hs
theorem measurable_shiftInvariantSigma_iff (ha : 0 < a) (J : GaugeField a → ℂ) :
    Measurable[shiftInvariantSigma a] J ↔
      Measurable[shiftInvariantSigma 1] (pullToUnit ha J) := by
  rw [← comap_shiftInvariantSigma ha]
  exact measurable_comap_iff_pullToUnit ha _ J
theorem shiftInvariantSigma_le (a : ℝ) :
    shiftInvariantSigma a ≤ (inferInstance : MeasurableSpace (GaugeField a)) :=
  fun _ hs => hs.1
theorem integrable_of_isBoundedObservable {A : GaugeField a → ℂ} (hA : IsBoundedObservable A)
    (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν] : Integrable A ν := by apply _root_.YangMills.Construction.LatticeConventions.CoarseStepFivePoint.integrable_of_isBoundedObservable <;> assumption
theorem pullToUnit_condExpShiftInvariant (ha : 0 < a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] {A : GaugeField a → ℂ} (hA : IsBoundedObservable A) :
    pullToUnit ha (condExpShiftInvariant ν A) =ᵐ[pushToUnit ν]
      condExpShiftInvariant (pushToUnit ν) (pullToUnit ha A) := by
  have := isProbabilityMeasure_pushToUnit ν
  have hD := measurableEmbedding_gaugeFieldRescale ha
  have hint : Integrable (pullToUnit ha (condExpShiftInvariant ν A)) (pushToUnit ν) := by
    refine hD.integrable_map_iff.2 ?_
    have e : pullToUnit ha (condExpShiftInvariant ν A) ∘ gaugeFieldRescale a =
        condExpShiftInvariant ν A := funext (pullToUnit_rescale ha _)
    rw [e]
    exact integrable_condExp
  refine ae_eq_condExp_of_forall_setIntegral_eq (shiftInvariantSigma_le 1)
    (integrable_of_isBoundedObservable (isBoundedObservable_pullToUnit ha hA) _)
    (fun s _ _ => hint.integrableOn) ?_ ?_
  · intro s hs _
    have hs' : MeasurableSet[shiftInvariantSigma a] (gaugeFieldRescale a ⁻¹' s) :=
      (isShiftInvariantSet_preimage_iff ha s).2 hs
    unfold pushToUnit
    rw [hD.setIntegral_map, hD.setIntegral_map]
    simp only [pullToUnit_rescale]
    exact setIntegral_condExp (shiftInvariantSigma_le a)
      (integrable_of_isBoundedObservable hA ν) hs'
  · have hm : Measurable[shiftInvariantSigma a] (condExpShiftInvariant ν A) :=
      stronglyMeasurable_condExp.measurable
    exact ((measurable_shiftInvariantSigma_iff ha _).1 hm).stronglyMeasurable.aestronglyMeasurable
theorem plateauPairing_eq_unit (ha : 0 < a) (ν : Measure (GaugeField a)) [IsProbabilityMeasure ν]
    {A B : GaugeField a → ℂ} (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    plateauPairing ν A B =
      ∫ U, conj (condExpShiftInvariant (pushToUnit ν) (pullToUnit ha A) U) *
        condExpShiftInvariant (pushToUnit ν) (pullToUnit ha B) U ∂pushToUnit ν := by
  have h₁ : plateauPairing ν A B = ∫ U, conj (pullToUnit ha (condExpShiftInvariant ν A) U) *
      pullToUnit ha (condExpShiftInvariant ν B) U ∂pushToUnit ν := by
    rw [integral_pushToUnit ha]
    simp only [pullToUnit_rescale]
    rfl
  rw [h₁]
  refine integral_congr_ae ?_
  filter_upwards [pullToUnit_condExpShiftInvariant ha ν hA,
    pullToUnit_condExpShiftInvariant ha ν hB] with U e₁ e₂
  rw [e₁, e₂]
theorem isShiftErgodic_pushToUnit_iff (ha : 0 < a) (ν : Measure (GaugeField a))
    [IsProbabilityMeasure ν] :
    IsShiftErgodic ν ↔ IsShiftErgodic (pushToUnit ν) := by
  have hD := measurableEmbedding_gaugeFieldRescale ha
  constructor
  · rintro ⟨_, h₂, h₃⟩
    refine ⟨isProbabilityMeasure_pushToUnit ν, (isShiftInvariant_pushToUnit_iff ha ν).1 h₂,
      fun I hI => ?_⟩
    have hI' : MeasurableSet[shiftInvariantSigma a] (gaugeFieldRescale a ⁻¹' I) :=
      (isShiftInvariantSet_preimage_iff ha I).2 hI
    unfold pushToUnit
    rw [hD.map_apply]
    exact h₃ _ hI'
  · rintro ⟨_, h₂, h₃⟩
    refine ⟨inferInstance, (isShiftInvariant_pushToUnit_iff ha ν).2 h₂, fun I hI => ?_⟩
    have hI' : MeasurableSet[shiftInvariantSigma 1] (gaugeFieldUnrescale ha ⁻¹' I) := by
      refine (isShiftInvariantSet_preimage_iff ha _).1 ?_
      rw [preimage_rescale_preimage_unrescale]
      exact hI
    have h := h₃ _ hI'
    unfold pushToUnit at h
    rwa [hD.map_apply, preimage_rescale_preimage_unrescale] at h
theorem transportsInvarianceAndErgodicity (ha : 0 < a) :
    TransportsInvarianceAndErgodicity ha := by
  intro ν
  have := ν.2
  refine ⟨fun r => isSymmetricUnder_toUnit_iff ha ν.1 r, isShiftInvariant_pushToUnit_iff ha ν.1,
    fun Q Q' hQ hQ' h => isLocallyReflectionPositive_toUnit_iff ha hQ hQ' h ν,
    fun J _ => measurable_shiftInvariantSigma_iff ha J,
    fun _ => ⟨fun A hA => pullToUnit_condExpShiftInvariant ha ν.1 hA,
      fun A B hA hB => plateauPairing_eq_unit ha ν.1 hA hB, isShiftErgodic_pushToUnit_iff ha ν.1⟩⟩
theorem pointOfUnit_injective (ha : 0 < a) :
    Function.Injective (pointOfUnit a) :=
  Function.LeftInverse.injective (pointToUnit_pointOfUnit ha)
def plaquetteOfUnit (a : ℝ) (p : ElementaryPlaquette 1) : ElementaryPlaquette a :=
  ⟨pointOfUnit a p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
def plaquetteToUnit (ha : 0 < a) (p : ElementaryPlaquette a) : ElementaryPlaquette 1 :=
  ⟨pointToUnit ha p.corner, p.lowAxis, p.highAxis, p.lowAxis_lt_highAxis⟩
theorem plaquetteOfUnit_plaquetteToUnit (ha : 0 < a) (p : ElementaryPlaquette a) :
    plaquetteOfUnit a (plaquetteToUnit ha p) = p :=
  ElementaryPlaquette.ext (pointOfUnit_pointToUnit ha p.corner) rfl rfl
theorem plaquetteOfUnit_injective (ha : 0 < a) :
    Function.Injective (plaquetteOfUnit a) := by
  intro p q h
  have h₁ := congrArg ElementaryPlaquette.corner h
  have h₂ := congrArg ElementaryPlaquette.lowAxis h
  have h₃ := congrArg ElementaryPlaquette.highAxis h
  exact ElementaryPlaquette.ext (pointOfUnit_injective ha h₁) h₂ h₃
theorem linkOfUnit_forwardFrom (x : LatticePoint 1) (μ : Fin 4) :
    linkOfUnit a (Link.forwardFrom x μ) = Link.forwardFrom (pointOfUnit a x) μ := by
  refine Link.ext rfl ?_
  change pointOfUnit a (x + axisStep 1 μ) = pointOfUnit a x + axisStep a μ
  rw [map_add, pointOfUnit_axisStep]
theorem faceEnergy_rescale (U : GaugeField a) (p : ElementaryPlaquette 1) :
    faceEnergy (gaugeFieldRescale a U) p =
      faceEnergy U (plaquetteOfUnit a p) := by
  have e : faceHolonomy (gaugeFieldRescale a U) p =
      faceHolonomy U (plaquetteOfUnit a p) := by
    change U (linkOfUnit a (Link.forwardFrom p.corner p.lowAxis)) *
        U (linkOfUnit a (Link.forwardFrom (p.corner + axisStep 1 p.lowAxis) p.highAxis)) *
        (U (linkOfUnit a (Link.forwardFrom (p.corner + axisStep 1 p.highAxis) p.lowAxis)))⁻¹ *
        (U (linkOfUnit a (Link.forwardFrom p.corner p.highAxis)))⁻¹ = _
    simp only [linkOfUnit_forwardFrom, map_add, pointOfUnit_axisStep]
    rfl
  unfold faceEnergy
  rw [e]
theorem linkOfUnit_mem_positiveLinks_iff (ha : 0 < a) (b : Link 1) :
    linkOfUnit a b ∈ positiveLinkSet a ↔ b ∈ positiveLinkSet 1 := by
  rw [mem_positiveLinks_iff, mem_positiveLinks_iff]
  have e : (linkOfUnit a b).terminal - (linkOfUnit a b).initial =
      pointOfUnit a (b.terminal - b.initial) := (map_sub _ _ _).symm
  constructor
  · rintro ⟨μ, h⟩
    refine ⟨μ, pointOfUnit_injective ha ?_⟩
    rw [← e, h, pointOfUnit_axisStep]
  · rintro ⟨μ, h⟩
    refine ⟨μ, ?_⟩
    rw [e, h, pointOfUnit_axisStep]
theorem pointOfUnit_mem_cornerSet_iff (ha : 0 < a) (x : LatticePoint 1)
    (p : ElementaryPlaquette 1) :
    pointOfUnit a x ∈ (plaquetteOfUnit a p).cornerSet ↔ x ∈ p.cornerSet := by
  have hs : ∀ μ, axisStep a μ = pointOfUnit a (axisStep 1 μ) :=
    fun μ => (pointOfUnit_axisStep a μ).symm
  simp only [ElementaryPlaquette.cornerSet, mem_insert_iff, mem_singleton_iff, plaquetteOfUnit,
    hs, ← map_add, (pointOfUnit_injective ha).eq_iff]
theorem linkOfUnit_mem_edgesOf_iff (ha : 0 < a) (b : Link 1) (p : ElementaryPlaquette 1) :
    linkOfUnit a b ∈ edgesOf (plaquetteOfUnit a p) ↔ b ∈ edgesOf p :=
  and_congr (linkOfUnit_mem_positiveLinks_iff ha b)
    (and_congr (pointOfUnit_mem_cornerSet_iff ha _ p)
      (pointOfUnit_mem_cornerSet_iff ha _ p))
theorem exists_linkOfUnit (ha : 0 < a) (b : Link a) :
    ∃ c : Link 1, linkOfUnit a c = b :=
  ⟨_, linkOfUnit_linkToUnit ha b⟩
theorem plaquetteOfUnit_mem_plaquettesTouching_iff (ha : 0 < a) {𝓛 : Finset (Link 1)}
    {𝓛' : Finset (Link a)} (hS : ∀ b, b ∈ 𝓛 ↔ linkOfUnit a b ∈ 𝓛') (p : ElementaryPlaquette 1) :
    plaquetteOfUnit a p ∈ plaquettesTouching 𝓛' ↔ p ∈ plaquettesTouching 𝓛 := by
  constructor
  · rintro ⟨b', hb, h⟩
    obtain ⟨b, rfl⟩ := exists_linkOfUnit ha b'
    refine ⟨b, (linkOfUnit_mem_edgesOf_iff ha b p).1 hb, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hS b).2 h)
    · exact Or.inr ((hS b.opposite).2 h)
  · rintro ⟨b, hb, h⟩
    refine ⟨linkOfUnit a b, (linkOfUnit_mem_edgesOf_iff ha b p).2 hb, ?_⟩
    rcases h with h | h
    · exact Or.inl ((hS b).1 h)
    · exact Or.inr ((hS b.opposite).1 h)
theorem wilsonLinkEnergy_rescale (ha : 0 < a) (β : ℝ) {𝓛 : Finset (Link 1)}
    {𝓛' : Finset (Link a)} (hS : ∀ b, b ∈ 𝓛 ↔ linkOfUnit a b ∈ 𝓛')
    (U : GaugeField a) :
    wilsonLinkEnergy β 𝓛 (gaugeFieldRescale a U) =
      wilsonLinkEnergy β 𝓛' U := by
  unfold wilsonLinkEnergy
  congr 1
  refine finsum_mem_eq_of_bijOn (plaquetteOfUnit a)
    ⟨fun p hp => (plaquetteOfUnit_mem_plaquettesTouching_iff ha hS p).2 hp,
      (plaquetteOfUnit_injective ha).injOn, fun p hp => ?_⟩
    fun p _ => faceEnergy_rescale U p
  refine ⟨plaquetteToUnit ha p, ?_, plaquetteOfUnit_plaquetteToUnit ha p⟩
  refine (plaquetteOfUnit_mem_plaquettesTouching_iff ha hS _).1 ?_
  rw [plaquetteOfUnit_plaquetteToUnit]
  exact hp
section Reindexing
variable {𝓢 : Set (Link 1)} {𝓢' : Set (Link a)}
def linksEquivUnit (ha : 0 < a) (hS : ∀ b, b ∈ 𝓢 ↔ linkOfUnit a b ∈ 𝓢') : 𝓢 ≃ 𝓢' :=
  (linkEquivUnit ha).subtypeEquiv hS
theorem hasNoOppositePairs_iff (ha : 0 < a) (hS : ∀ b, b ∈ 𝓢 ↔ linkOfUnit a b ∈ 𝓢') :
    HasNoOppositePairs 𝓢 ↔ HasNoOppositePairs 𝓢' := by
  constructor
  · intro h b' hb' hr
    obtain ⟨b, rfl⟩ := exists_linkOfUnit ha b'
    exact h b ((hS b).2 hb') ((hS b.opposite).2 hr)
  · intro h b hb hr
    exact h _ ((hS b).1 hb) ((hS b.opposite).1 hr)
theorem rescale_overwriteLinks (ha : 0 < a) (hS : ∀ b, b ∈ 𝓢 ↔ linkOfUnit a b ∈ 𝓢')
    (h : HasNoOppositePairs 𝓢) (h' : HasNoOppositePairs 𝓢')
    (V : LinkVariables 𝓢') (U : GaugeField a) :
    gaugeFieldRescale a (overwriteLinks h' V U) =
      overwriteLinks h (fun c => V (linksEquivUnit ha hS c)) (gaugeFieldRescale a U) := by
  classical
  refine Subtype.ext (funext fun b => ?_)
  change (overwriteLinks h' V U).1 (linkOfUnit a b) =
    (overwriteLinks h (fun c => V (linksEquivUnit ha hS c)) (gaugeFieldRescale a U)).1 b
  by_cases hb : b ∈ 𝓢
  · have hb' := (hS b).1 hb
    simp only [overwriteLinks, dif_pos hb, dif_pos hb']
    rfl
  · have hb' : linkOfUnit a b ∉ 𝓢' := fun e => hb ((hS b).2 e)
    by_cases hr : b.opposite ∈ 𝓢
    · have hr' : (linkOfUnit a b).opposite ∈ 𝓢' := (hS b.opposite).1 hr
      simp only [overwriteLinks, dif_neg hb, dif_neg hb', dif_pos hr, dif_pos hr']
      rfl
    · have hr' : (linkOfUnit a b).opposite ∉ 𝓢' := fun e => hr ((hS b.opposite).2 e)
      simp only [overwriteLinks, dif_neg hb, dif_neg hb', dif_neg hr, dif_neg hr']
      rfl
end Reindexing
theorem integral_haarPi_reindex {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {A C : Type}
    [Countable A] [Countable C] (σ : A ≃ C) (g : (A → Matrices.ComplexMatrix2.specialUnitary) → E) :
    ∫ v, g (fun i => v (σ i)) ∂Matrices.ComplexMatrix2.haarPi C =
      ∫ w, g w ∂Matrices.ComplexMatrix2.haarPi A := by
  have hmap := Measure.infinitePi_map_piCongrLeft
    (X := fun _ : A => Matrices.ComplexMatrix2.specialUnitary)
    (μ := fun _ : A => Matrices.ComplexMatrix2.haarProb) σ.symm
  have hmp : MeasurePreserving
      (MeasurableEquiv.piCongrLeft (fun _ : A => Matrices.ComplexMatrix2.specialUnitary) σ.symm)
      (Matrices.ComplexMatrix2.haarPi C) (Matrices.ComplexMatrix2.haarPi A) :=
    ⟨MeasurableEquiv.measurable _, hmap⟩
  have hfun : ∀ v : C → Matrices.ComplexMatrix2.specialUnitary,
      (MeasurableEquiv.piCongrLeft (fun _ : A => Matrices.ComplexMatrix2.specialUnitary)
        σ.symm v) = fun i => v (σ i) := by
    intro v
    funext i
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]
  have h := hmp.integral_comp' g
  simpa only [hfun] using h
theorem wilsonLinkKernel_rescale (ha : 0 < a) (β : ℝ) {𝓛 : Finset (Link 1)}
    {𝓛' : Finset (Link a)} (hS : ∀ b, b ∈ 𝓛 ↔ linkOfUnit a b ∈ 𝓛')
    (h : HasNoOppositePairs (𝓛 : Set (Link 1)))
    (h' : HasNoOppositePairs (𝓛' : Set (Link a)))
    (F : GaugeField a → ℂ) (U : GaugeField a) :
    wilsonLinkKernel β 𝓛' h' F U =
      wilsonLinkKernel β 𝓛 h (pullToUnit ha F) (gaugeFieldRescale a U) := by
  have hS' : ∀ b, b ∈ (𝓛 : Set (Link 1)) ↔ linkOfUnit a b ∈ (𝓛' : Set (Link a)) := hS
  have hset := rescale_overwriteLinks ha hS' h h'
  have hnum := integral_haarPi_reindex (linksEquivUnit ha hS') fun V =>
    pullToUnit ha F (overwriteLinks h V (gaugeFieldRescale a U)) *
      (Real.exp (-wilsonLinkEnergy β 𝓛
        (overwriteLinks h V (gaugeFieldRescale a U))) : ℂ)
  have hden := integral_haarPi_reindex (linksEquivUnit ha hS') fun V =>
    Real.exp (-wilsonLinkEnergy β 𝓛 (overwriteLinks h V (gaugeFieldRescale a U)))
  simp only [← hset, pullToUnit_rescale, wilsonLinkEnergy_rescale ha β hS] at hnum hden
  unfold wilsonLinkKernel linkKernel LinkVariables.haarMeasure
  rw [hnum, hden]
theorem preservesBoundedMeasurable_pushToUnit_iff (ha : 0 < a) (β : ℝ)
    (ν : Measure (GaugeField a)) :
    AnyOrientationGibbs.PreservesBoundedMeasurable β ν ↔
      AnyOrientationGibbs.PreservesBoundedMeasurable β (pushToUnit ν) := by
  constructor
  · intro hK 𝓛 h F' hF'
    have hS : ∀ b, b ∈ 𝓛 ↔
        linkOfUnit a b ∈ 𝓛.map (linkEquivUnit ha).toEmbedding :=
      fun b => (Finset.mem_map' (linkEquivUnit ha).toEmbedding).symm
    have h' : HasNoOppositePairs
        ((𝓛.map (linkEquivUnit ha).toEmbedding : Finset (Link a)) : Set (Link a)) :=
      (hasNoOppositePairs_iff ha hS).1 h
    have e := pullToUnit_comp_rescale ha F'
    have hk := hK _ h' (F' ∘ gaugeFieldRescale a) (isBoundedObservable_comp_rescale hF')
    simp only [wilsonLinkKernel_rescale ha β hS h h', e] at hk
    rw [integral_pushToUnit ha, integral_pushToUnit ha]
    exact hk
  · intro hK 𝓛' h' F hF
    have hS : ∀ b, b ∈ 𝓛'.map (linkEquivUnit ha).symm.toEmbedding ↔
        linkOfUnit a b ∈ 𝓛' :=
      fun b => Finset.mem_map_equiv
    have h : HasNoOppositePairs
        ((𝓛'.map (linkEquivUnit ha).symm.toEmbedding : Finset (Link 1)) : Set (Link 1)) :=
      (hasNoOppositePairs_iff ha hS).2 h'
    have hk := hK _ h (pullToUnit ha F) (isBoundedObservable_pullToUnit ha hF)
    rw [integral_pushToUnit ha, integral_pullToUnit ha] at hk
    simp only [wilsonLinkKernel_rescale ha β hS h h']
    exact hk
def pointAddEquivUnit (ha : 0 < a) : LatticePoint a ≃+ LatticePoint 1 where
  toFun := pointToUnit ha
  invFun := pointOfUnit a
  left_inv := pointOfUnit_pointToUnit ha
  right_inv := pointToUnit_pointOfUnit ha
  map_add' := map_add _
theorem isSymmetricUnder_shift_toUnit_iff (ha : 0 < a) (ν : Measure (GaugeField a))
    (v : LatticePoint a) :
    IsSymmetricUnder ν (shift v) ↔
      IsSymmetricUnder (pushToUnit ν) (shift (pointToUnit ha v)) := by
  rw [← toUnit_shift]
  exact isSymmetricUnder_toUnit_iff ha ν _
theorem isPeriodicMeasure_pushToUnit_iff (ha : 0 < a) (ν : Measure (GaugeField a)) :
    IsPeriodicMeasure ν ↔ IsPeriodicMeasure (pushToUnit ν) := by
  constructor
  · rintro ⟨H, hH, hv⟩
    have hs : Function.Surjective (pointOfUnit a) := (pointAddEquivUnit ha).symm.surjective
    refine ⟨H.comap (pointOfUnit a), ⟨?_⟩, fun v' hv' => ?_⟩
    · rw [AddSubgroup.index_comap_of_surjective _ hs]
      exact hH.index_ne_zero
    · have h := (isSymmetricUnder_shift_toUnit_iff ha ν _).1 (hv _ hv')
      rwa [pointToUnit_pointOfUnit] at h
  · rintro ⟨H, hH, hv⟩
    refine ⟨H.comap (pointToUnit ha), ⟨?_⟩, fun v h => ?_⟩
    · rw [AddSubgroup.index_comap_of_surjective _ (pointToUnit_surjective ha)]
      exact hH.index_ne_zero
    · exact (isSymmetricUnder_shift_toUnit_iff ha ν v).2 (hv _ h)
theorem transportsGibbsMeasures (ha : 0 < a) {β : ℝ} (hβ : 0 < β)
    (hBorel : AnyOrientationGibbs.Equivalences) :
    TransportsGibbsMeasures a β := by
  intro ν
  have := ν.2
  have hp : IsProbabilityMeasure (pushToUnit ν.1) := isProbabilityMeasure_pushToUnit ν.1
  have hG : IsGibbs β ν.1 ↔ IsGibbs β (pushToUnit ν.1) :=
    ((hBorel a β ha hβ ν.1 inferInstance).out 0 2).trans
      ((preservesBoundedMeasurable_pushToUnit_iff ha β ν.1).trans
        ((hBorel 1 β one_pos hβ (pushToUnit ν.1) hp).out 0 2).symm)
  have hP := isPeriodicMeasure_pushToUnit_iff ha ν.1
  exact ⟨hG, hP, fun _ => and_congr hG hP⟩
theorem toUnit_mem_reflectionPositiveSet (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) : BorelProb.toUnit ν ∈ reflectionPositiveSet 1 := by
  refine ⟨(isShiftInvariant_pushToUnit_iff ha ν.1).1 hν.1, fun Q' hQ' => ?_⟩
  have hpair : IsScaledPair a ⟨Q'.normal, a * Q'.level, Q'.normal_valid⟩ Q' :=
    ⟨rfl, by field_simp⟩
  have hQ := (isLatticeMirror_iff_of_scaled ha hpair).2 hQ'
  exact (isLocallyReflectionPositive_toUnit_iff ha hQ hQ' hpair ν).1 (hν.2 _ hQ)
theorem unitSpacingTransport_holds (hBorel : AnyOrientationGibbs.Equivalences)
    (hMoves : SymmetriesTransportLinksSupportsAndPlaquettes) : UnitSpacingTransport :=
  fun _ ha => ⟨transportsFieldsObservablesMeasures ha, transportsSymmetriesAndMirrors ha hMoves,
    transportsInvarianceAndErgodicity ha, fun _ hβ => transportsGibbsMeasures ha hβ hBorel,
    fun _ hν => toUnit_mem_reflectionPositiveSet ha hν⟩
end GibbsAtFixedSpacing.ScalingToUnitSpacing
end YangMills.Construction
end
