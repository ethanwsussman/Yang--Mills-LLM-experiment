import YangMills.Construction.InfiniteLattice.DilationCarriesStatesToSpacingOneProof
import YangMills.Construction.InfiniteLattice.EquilibriumEquationsAndTheDilation
import YangMills.Construction.InfiniteLattice.PeriodicGibbsStatesAndPlaquettesAtEverySpacing
import YangMills.Construction.InfiniteLattice.PureAndErgodicPeriodicGibbsStates
import YangMills.Construction.ReflectionPositivity.DilationOnOneLattice
import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped Pointwise
noncomputable section
namespace YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.CutoffLattice (faceLinks restrictField)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair unitPositiveClass)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (IsErgodicState
  reflectionPositiveSet)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
  (TransportsInvariantSets TransportsMeasuresAndSymmetries TransportsMirrors TransportsObservables
  TransportsStateClass IsRescaledMirror)
open YangMills.Construction.InfiniteLattice.GibbsEquations (DLREquations
  ConditionalAverageProperties FacesUnderRescaling ConditionalAverageUnderRescaling)
open YangMills.Construction.InfiniteLattice.CutoffStructure (IsContinuousInLinks)
variable {a : ℝ}
theorem gaugeFieldUnrescale_rescale (ha : 0 < a) (U : GaugeField a) :
    gaugeFieldUnrescale ha (gaugeFieldRescale a U) = U :=
  (gaugeFieldEquivUnit ha).left_inv U
theorem gaugeFieldRescale_unrescale (ha : 0 < a) (U : GaugeField 1) :
    gaugeFieldRescale a (gaugeFieldUnrescale ha U) = U :=
  (gaugeFieldEquivUnit ha).right_inv U
theorem measurable_gaugeFieldRescale (a : ℝ) : Measurable (gaugeFieldRescale a) :=
  (continuous_gaugeFieldRescale a).measurable
theorem measurable_gaugeFieldUnrescale {ha : 0 < a} (hS : TransportsObservables ha) :
    Measurable (gaugeFieldUnrescale ha) := by
  obtain ⟨⟨e, -, he⟩, -⟩ := hS
  rw [← he]
  exact e.symm.continuous.measurable
theorem pushToUnit_injective {ha : 0 < a} (hS : TransportsObservables ha)
    {ν ν' : Measure (GaugeField a)} (h : pushToUnit ν = pushToUnit ν') : ν = ν' := by
  have key : ∀ ρ : Measure (GaugeField a),
      (pushToUnit ρ).map (gaugeFieldUnrescale ha) = ρ := fun ρ => by
    rw [pushToUnit, Measure.map_map (measurable_gaugeFieldUnrescale hS)
      (measurable_gaugeFieldRescale a)]
    have : gaugeFieldUnrescale ha ∘ gaugeFieldRescale a = id :=
      funext (gaugeFieldUnrescale_rescale ha)
    rw [this, Measure.map_id]
  rw [← key ν, h, key]
theorem pushToUnit_surjective {ha : 0 < a} (hS : TransportsObservables ha)
    (ν' : Measure (GaugeField 1)) : ∃ ν : Measure (GaugeField a), pushToUnit ν = ν' := by
  refine ⟨ν'.map (gaugeFieldUnrescale ha), ?_⟩
  rw [pushToUnit, Measure.map_map (measurable_gaugeFieldRescale a)
    (measurable_gaugeFieldUnrescale hS)]
  have : gaugeFieldRescale a ∘ gaugeFieldUnrescale ha = id :=
    funext (gaugeFieldRescale_unrescale ha)
  rw [this, Measure.map_id]
theorem pushToUnit_add_smul (s t : ENNReal) (ν₁ ν₂ : Measure (GaugeField a)) :
    pushToUnit (s • ν₁ + t • ν₂) = s • pushToUnit ν₁ + t • pushToUnit ν₂ := by
  simp only [pushToUnit]
  rw [Measure.map_add _ _ (measurable_gaugeFieldRescale a), Measure.map_smul, Measure.map_smul]
theorem isProbabilityMeasure_of_pushToUnit {ν : Measure (GaugeField a)}
    (h : IsProbabilityMeasure (pushToUnit ν)) : IsProbabilityMeasure ν := by
  refine ⟨?_⟩
  have h1 := h.measure_univ
  rwa [pushToUnit, Measure.map_apply (measurable_gaugeFieldRescale a) MeasurableSet.univ,
    preimage_univ] at h1
def emptyLinkWindow (a : ℝ) : LinkWindow a := ⟨∅, by simp⟩
open Classical in
theorem exists_rescaleToUnit_eq (ha : 0 < a) (W' : LinkWindow 1) :
    ∃ W : LinkWindow a, W.rescaleToUnit ha = W' := by
  refine ⟨⟨W'.links.image (linkOfUnit a), ?_⟩, ?_⟩
  · intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨μ, hμ⟩ := W'.isPositive b' hb'
    refine ⟨μ, ?_⟩
    change pointOfUnit a b'.terminal - pointOfUnit a b'.initial = axisStep a μ
    rw [← map_sub, hμ, pointOfUnit_axisStep]
  · cases W' with
    | mk ls hpos =>
      simp only [LinkWindow.rescaleToUnit, LinkWindow.mk.injEq]
      rw [Finset.image_image]
      have : linkToUnit ha ∘ linkOfUnit a = id :=
        funext (linkEquivUnit ha).left_inv
      rw [this, Finset.image_id]
theorem isGibbs_iff_pushToUnit {ha : 0 < a} {β : ℝ} (hS : TransportsObservables ha)
    (hM : TransportsMeasuresAndSymmetries ha)
    (hOp : ∀ W : LinkWindow a, ConditionalAverageProperties ha β W)
    (hEa : DLREquations ha β) (hE1 : DLREquations (one_pos : (0 : ℝ) < 1) β)
    (hSpec : ∀ W : LinkWindow a, ConditionalAverageUnderRescaling ha β W) (ν : BorelProb a) :
    IsGibbs β ν.1 ↔ IsGibbs β (pushToUnit ν.1) := by
  obtain ⟨-, hbij, -, hDF, -⟩ := hS
  obtain ⟨-, hint, -⟩ := hM
  refine (hEa ν).trans (Iff.trans ?_ (hE1 (BorelProb.toUnit ν)).symm)
  constructor
  · intro h W' F' hF'
    obtain ⟨W, rfl⟩ := exists_rescaleToUnit_eq ha W'
    obtain ⟨hob, hback⟩ := hDF F' hF'
    have h1 := hSpec W _ hob
    rw [hback] at h1
    rw [← h1, hint ν _ ((hOp W).1 _ hob).1, h W _ hob]
    have h2 := hint ν _ hob
    rw [hback] at h2
    exact h2.symm
  · intro h W F hF
    have hfo : IsBoundedObservable (pullToUnit ha F) := hbij.mapsTo hF
    rw [← hint ν _ ((hOp W).1 F hF).1, hSpec W F hF, h _ _ hfo, hint ν F hF]
theorem isPeriodicGibbs_iff_pushToUnit {ha : 0 < a} {β : ℝ}
    (hG : ∀ ν : BorelProb a, IsGibbs β ν.1 ↔ IsGibbs β (pushToUnit ν.1))
    (hC : TransportsStateClass ha) (ν : Measure (GaugeField a)) :
    IsPeriodicGibbs β ν ↔ IsPeriodicGibbs β (pushToUnit ν) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    have hp : IsProbabilityMeasure ν := h₁.1
    exact ⟨(hG ⟨ν, hp⟩).1 h₁, ((hC ⟨ν, hp⟩).2.2.1).1 h₂⟩
  · rintro ⟨h₁, h₂⟩
    have hp : IsProbabilityMeasure ν := isProbabilityMeasure_of_pushToUnit h₁.1
    exact ⟨(hG ⟨ν, hp⟩).2 h₁, ((hC ⟨ν, hp⟩).2.2.1).2 h₂⟩
theorem isExtremalPeriodicGibbs_iff_pushToUnit {ha : 0 < a} {β : ℝ}
    (hS : TransportsObservables ha)
    (hPG : ∀ ν : Measure (GaugeField a),
      IsPeriodicGibbs β ν ↔ IsPeriodicGibbs β (pushToUnit ν))
    (ν : Measure (GaugeField a)) :
    IsExtremalPeriodicGibbs β ν ↔ IsExtremalPeriodicGibbs β (pushToUnit ν) := by
  constructor
  · rintro ⟨hν, h⟩
    refine ⟨(hPG ν).1 hν, fun ν₁' ν₂' h₁ h₂ t h0 h1 e => ?_⟩
    obtain ⟨ν₁, rfl⟩ := pushToUnit_surjective hS ν₁'
    obtain ⟨ν₂, rfl⟩ := pushToUnit_surjective hS ν₂'
    have e' := pushToUnit_injective hS (e.trans (pushToUnit_add_smul _ _ ν₁ ν₂).symm)
    obtain ⟨e₁, e₂⟩ := h ν₁ ν₂ ((hPG _).2 h₁) ((hPG _).2 h₂) t h0 h1 e'
    exact ⟨by rw [e₁], by rw [e₂]⟩
  · rintro ⟨hν, h⟩
    refine ⟨(hPG ν).2 hν, fun ν₁ ν₂ h₁ h₂ t h0 h1 e => ?_⟩
    obtain ⟨e₁, e₂⟩ := h _ _ ((hPG _).1 h₁) ((hPG _).1 h₂) t h0 h1
      (by rw [e, pushToUnit_add_smul])
    exact ⟨pushToUnit_injective hS e₁, pushToUnit_injective hS e₂⟩
theorem toFun_eq_smul_toUnit (ha : 0 < a) (r : LatticeSymmetry a) (x : AmbientSpace) :
    r.toFun x = a • (r.toUnit ha).toFun (a⁻¹ • x) := by
  change _ = a • (a⁻¹ • r.toFun (a • a⁻¹ • x))
  rw [smul_inv_smul₀ ha.ne', smul_inv_smul₀ ha.ne']
theorem symmetriesAreLatticeMotions (ha : 0 < a)
    (hU : UnitSymmetriesAndFaces.SymmetriesAreAffineMotions)
    (hflat : ∀ t : LatticeSymmetry 1, ∃! r : LatticeSymmetry a, r.toUnit ha = t) :
    SymmetriesAreLatticeMotions a := by
  refine ⟨fun s => ⟨?_, ?_⟩, hU.2⟩
  · rintro ⟨r, rfl⟩
    obtain ⟨w, hw, v, hv⟩ := (hU.1 (r.toUnit ha).toFun).1 ⟨r.toUnit ha, rfl⟩
    refine ⟨w, hw, pointOfUnit a v, funext fun x => ?_⟩
    rw [toFun_eq_smul_toUnit ha r x, hv]
    change a • (w (a⁻¹ • x) + (v : AmbientSpace)) = w x + a • (v : AmbientSpace)
    rw [smul_add, map_smul, smul_inv_smul₀ ha.ne']
  · rintro ⟨w, hw, v, rfl⟩
    obtain ⟨t, ht⟩ := (hU.1 (latticeMotion w (pointToUnit ha v))).2 ⟨w, hw, _, rfl⟩
    obtain ⟨r, hr, -⟩ := hflat t
    refine ⟨r, funext fun x => ?_⟩
    rw [toFun_eq_smul_toUnit ha r x, hr, ht]
    change a • (w (a⁻¹ • x) + a⁻¹ • (v : AmbientSpace)) = w x + v
    rw [map_smul, smul_add, smul_inv_smul₀ ha.ne', smul_inv_smul₀ ha.ne']
theorem toUnit_mem_unitPositiveClass {ha : 0 < a} (hC : TransportsStateClass ha)
    (hOne : ReflectionPositivity.HalfAndShift.PositiveClassCharUnit) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) :
    (GibbsAtFixedSpacing.BorelProb.toUnit ν).1 ∈ unitPositiveClass := by
  have h := ((hC ν).2.2.2.2).1 hν
  rw [← hOne]
  exact ⟨_, h, rfl⟩
theorem toUnit_pointMap (ha : 0 < a) (r : LatticeSymmetry a) (x : LatticePoint a) :
    (r.toUnit ha).pointMap (pointToUnit ha x) = pointToUnit ha (r.pointMap x) := by
  apply Subtype.ext
  change inverseScaling ha (r.toFun ((inverseScaling ha).symm (inverseScaling ha x))) =
    inverseScaling ha (r.toFun x)
  rw [Equiv.symm_apply_apply]
theorem pointToUnit_injective (ha : 0 < a) :
    Function.Injective (pointToUnit ha) := fun _ _ h =>
  Subtype.ext ((inverseScaling ha).injective (congrArg Subtype.val h))
theorem gaugeFieldRescale_pullbackField (ha : 0 < a) (r : LatticeSymmetry a) (U : GaugeField a) :
    gaugeFieldRescale a (r.pullbackField U) =
      (r.toUnit ha).pullbackField (gaugeFieldRescale a U) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.ScalingToUnitSpacing.rescale_pullbackField <;> assumption
theorem linkOfUnit_forwardFrom (x : LatticePoint 1) (μ : Fin 4) :
    linkOfUnit a (Link.forwardFrom x μ) = Link.forwardFrom (pointOfUnit a x) μ := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.ScalingToUnitSpacing.linkOfUnit_forwardFrom <;> assumption
theorem pointOfUnit_pointRescale (ha : 0 < a) (x : LatticePoint a) :
    pointOfUnit a (pointRescale ha x) = x :=
  Subtype.ext (smul_inv_smul₀ ha.ne' _)
theorem linkOfUnit_mem_faceLinks (ha : 0 < a) (p : ElementaryPlaquette a) {b : Link 1}
    (hb : b ∈ faceLinks (rescaledPlaquette ha p)) : linkOfUnit a b ∈ faceLinks p := by
  have hcorner : (rescaledPlaquette ha p).corner = pointRescale ha p.corner := rfl
  have hlow : (rescaledPlaquette ha p).lowAxis = p.lowAxis := rfl
  have hhigh : (rescaledPlaquette ha p).highAxis = p.highAxis := rfl
  simp only [faceLinks, mem_ofPred_eq, ElementaryPlaquette.edges, List.mem_cons,
    List.not_mem_nil, or_false, hcorner, hlow, hhigh] at hb ⊢
  rcases hb with rfl | rfl | rfl | rfl <;>
    simp [linkOfUnit_forwardFrom, map_add, pointOfUnit_pointRescale, pointOfUnit_axisStep]
theorem faceEnergy_rescale (ha : 0 < a) {p : ElementaryPlaquette a}
    (hp : pullToUnit ha (fun U : GaugeField a => faceEnergy U p) =
      fun U' : GaugeField 1 => faceEnergy U' (rescaledPlaquette ha p))
    (U : GaugeField a) :
    faceEnergy (gaugeFieldRescale a U) (rescaledPlaquette ha p) = faceEnergy U p := by
  have h := congrFun hp (gaugeFieldRescale a U)
  change faceEnergy (gaugeFieldUnrescale ha (gaugeFieldRescale a U)) p = _ at h
  rw [gaugeFieldUnrescale_rescale] at h
  exact h.symm
theorem cornerSet_plaquetteMap (r : LatticeSymmetry a) {p : ElementaryPlaquette a}
    (h : ∃ q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet) :
    (r.plaquetteMap p).cornerSet = r.pointMap '' p.cornerSet := by
  rw [LatticeSymmetry.plaquetteMap, dif_pos h]
  exact h.choose_spec
structure FacesCorrespond (ha : 0 < a) : Prop where
  cornerSet_eq : ∀ p : ElementaryPlaquette a,
    pointToUnit ha '' p.cornerSet = (rescaledPlaquette ha p).cornerSet
  existsUnique : ∀ q : ElementaryPlaquette 1, ∃! p : ElementaryPlaquette a, rescaledPlaquette ha p = q
theorem FacesCorrespond.injective {ha : 0 < a} (h : FacesCorrespond ha) :
    Function.Injective (rescaledPlaquette ha) := fun _ _ e =>
  (h.existsUnique _).unique rfl e.symm
theorem image_toUnit_pointMap (ha : 0 < a) (h : FacesCorrespond ha) (r : LatticeSymmetry a)
    (p : ElementaryPlaquette a) :
    (r.toUnit ha).pointMap '' (rescaledPlaquette ha p).cornerSet =
      pointToUnit ha '' (r.pointMap '' p.cornerSet) := by
  rw [← h.cornerSet_eq p, image_image, image_image]
  exact image_congr fun x _ => toUnit_pointMap ha r x
theorem existsUnique_plaquette_image (ha : 0 < a) (h : FacesCorrespond ha)
    (hM : UnitSymmetriesAndFaces.SymmetriesMapFaces) (r : LatticeSymmetry a)
    (p : ElementaryPlaquette a) :
    ∃! q : ElementaryPlaquette a, q.cornerSet = r.pointMap '' p.cornerSet := by
  obtain ⟨⟨q', hq', huniq⟩, -⟩ := hM (r.toUnit ha) (rescaledPlaquette ha p)
  obtain ⟨q, hq, -⟩ := h.existsUnique q'
  have hq'' : q'.cornerSet = (r.toUnit ha).pointMap '' (rescaledPlaquette ha p).cornerSet := hq'
  refine ⟨q, ?_, fun q₂ h₂ => ?_⟩
  · refine image_injective.2 (pointToUnit_injective ha) ?_
    rw [h.cornerSet_eq q, hq, hq'', image_toUnit_pointMap ha h]
  · refine h.injective ((huniq _ ?_).trans hq.symm)
    change (rescaledPlaquette ha q₂).cornerSet = _
    rw [← h.cornerSet_eq q₂, h₂, image_toUnit_pointMap ha h]
theorem rescaledPlaquette_plaquetteMap (ha : 0 < a) (h : FacesCorrespond ha)
    (hM : UnitSymmetriesAndFaces.SymmetriesMapFaces) (r : LatticeSymmetry a)
    (p : ElementaryPlaquette a) :
    rescaledPlaquette ha (r.plaquetteMap p) =
      (r.toUnit ha).plaquetteMap (rescaledPlaquette ha p) := by
  obtain ⟨⟨q', -, huniq⟩, hc, -⟩ := hM (r.toUnit ha) (rescaledPlaquette ha p)
  have hex := existsUnique_plaquette_image ha h hM r p
  refine (huniq _ ?_).trans (huniq _ hc).symm
  change (rescaledPlaquette ha (r.plaquetteMap p)).cornerSet = _
  rw [← h.cornerSet_eq, cornerSet_plaquetteMap r hex.exists, image_toUnit_pointMap ha h]
theorem holds (hGroup : UnitSymmetriesAndFaces.Summary)
    (hDil : ReflectionPositivity.LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hEq : GibbsEquations.GibbsEquationsAndRescaling)
    (hSides : ReflectionPositivity.HalfAndShift.HalfAndShiftStatement)
    (hPure : ExtremalErgodicPeriodicGibbsStatement) : Statement := by
  intro a ha
  obtain ⟨hS, hM, hMir, hC, hI⟩ := hDil a ha
  obtain ⟨hUMotions, hUInv, hUCont, hUMove, hUTrans, hUMeans⟩ := hGroup
  have hOne := hSides.2
  have hflat : ∀ t : LatticeSymmetry 1, ∃! r : LatticeSymmetry a, r.toUnit ha = t :=
    hM.2.2.2.2.2.2.2.1
  have hPl : FacesUnderRescaling ha (emptyLinkWindow a) :=
    (hEq a ha 1 one_pos (emptyLinkWindow a)).1
  have hPl1 : FacesUnderRescaling (one_pos : (0 : ℝ) < 1) (emptyLinkWindow 1) :=
    (hEq 1 one_pos 1 one_pos (emptyLinkWindow 1)).1
  have hCorr : FacesCorrespond ha :=
    ⟨fun p => ((hPl.1 p).2.2.1), hPl.2⟩
  have hAct : ∀ (p : ElementaryPlaquette a) (U : GaugeField a),
      faceEnergy (gaugeFieldRescale a U) (rescaledPlaquette ha p) = faceEnergy U p := fun p U =>
    faceEnergy_rescale ha (hPl.1 p).2.2.2.2.1 U
  have hG : ∀ β : ℝ, 0 < β → ∀ ν : BorelProb a,
      IsGibbs β ν.1 ↔ IsGibbs β (pushToUnit ν.1) := fun β hβ ν =>
    isGibbs_iff_pushToUnit hS hM (fun W => (hEq a ha β hβ W).2.1)
      (hEq a ha β hβ (emptyLinkWindow a)).2.2.1 (hEq 1 one_pos β hβ (emptyLinkWindow 1)).2.2.1
      (fun W => (hEq a ha β hβ W).2.2.2) ν
  have hPG : ∀ β : ℝ, 0 < β → ∀ ν : Measure (GaugeField a),
      IsPeriodicGibbs β ν ↔ IsPeriodicGibbs β (pushToUnit ν) := fun β hβ =>
    isPeriodicGibbs_iff_pushToUnit (hG β hβ) hC
  have hPu : ∀ β : ℝ, 0 < β → ∀ ν : Measure (GaugeField a),
      IsExtremalPeriodicGibbs β ν ↔ IsExtremalPeriodicGibbs β (pushToUnit ν) := fun β hβ =>
    isExtremalPeriodicGibbs_iff_pushToUnit hS (hPG β hβ)
  refine ⟨?_, ?_, symmetriesAreLatticeMotions ha hUMotions hflat, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ν P β hβ
    have hdm : IsRescaledMirror P (rescaledMirror ha P) := ⟨rfl, rfl⟩
    have himg : a⁻¹ • P.hyperplane = inverseScaling ha '' P.hyperplane := rfl
    refine ⟨(hC ν).2.1, ⟨?_, himg, ((hC ν).2.2.2.1 P _ hdm).2.2⟩, hG β hβ ν, hPG β hβ _,
      hPu β hβ _, (hI.2.2.2 ν).2.1⟩
    rw [himg]
    exact ((hMir.2.2 P _ hdm).1).symm
  · intro ν F hF
    refine ⟨(integral_map (measurable_gaugeFieldRescale a).aemeasurable
      hF.1.aestronglyMeasurable).symm, fun hT => ?_⟩
    obtain ⟨hob, hback⟩ := hS.2.2.2.1 F hF
    have h := ((hI.2.2.2 ν).2.2 hT _ _ hob hob).1
    rw [hback] at h
    have h' := ae_of_ae_map (measurable_gaugeFieldRescale a).aemeasurable h
    filter_upwards [h'] with U hU
    have e : pullToUnit ha (condExpShiftInvariant ν.1 (F ∘ gaugeFieldRescale a))
        (gaugeFieldRescale a U) =
        condExpShiftInvariant ν.1 (F ∘ gaugeFieldRescale a) U := by
      change condExpShiftInvariant ν.1 (F ∘ gaugeFieldRescale a)
        (gaugeFieldUnrescale ha (gaugeFieldRescale a U)) = _
      rw [gaugeFieldUnrescale_rescale]
    rw [← e]
    exact hU
  · intro ν hν r
    exact ((hC ν).1 r).2 (hUInv _ (toUnit_mem_unitPositiveClass hC hOne hν) (r.toUnit ha))
  · intro p
    obtain ⟨⟨g, hg, hgU⟩, -⟩ := hUCont (rescaledPlaquette ha p)
    refine ⟨⟨fun V => g fun b => V ⟨linkOfUnit a b, linkOfUnit_mem_faceLinks ha p b.2⟩,
      hg.comp (continuous_pi fun b => continuous_apply _), fun U => ?_⟩, fun U => ?_⟩
    · exact (hAct p U).symm.trans (hgU (gaugeFieldRescale a U))
    · exact (hPl.1 p).2.1 U
  · intro r p
    obtain ⟨-, -, hb, hA⟩ := hUMove (r.toUnit ha) (rescaledPlaquette ha p)
    have hex := existsUnique_plaquette_image ha hCorr hUMove r p
    have hK := rescaledPlaquette_plaquetteMap ha hCorr hUMove r p
    refine ⟨hex, cornerSet_plaquetteMap r hex.exists, ?_, ?_⟩
    · apply (inverseScaling ha).injective
      rw [← (hPl.1 _).2.2.2.1, hK, hb, (hPl.1 p).2.2.2.1]
      change inverseScaling ha (r.toFun ((inverseScaling ha).symm (inverseScaling ha p.center))) = _
      rw [Equiv.symm_apply_apply]
    · funext U
      change faceEnergy (r.pullbackField U) p = faceEnergy U (r.plaquetteMap p)
      rw [← hAct p (r.pullbackField U), gaugeFieldRescale_pullbackField ha,
        ← hAct (r.plaquetteMap p) U, hK]
      exact congrFun hA (gaugeFieldRescale a U)
  · intro p p'
    obtain ⟨t, ht⟩ := hUTrans (rescaledPlaquette ha p) (rescaledPlaquette ha p')
    obtain ⟨r, rfl, -⟩ := hflat t
    refine ⟨r, hCorr.injective ?_⟩
    rw [rescaledPlaquette_plaquetteMap ha hCorr hUMove, ht]
  · intro ν hν p p'
    have hmean : ∀ q : ElementaryPlaquette a, ∫ U : GaugeField a, faceEnergy U q ∂ν.1 =
        ∫ U : GaugeField 1, faceEnergy U (rescaledPlaquette ha q) ∂(pushToUnit ν.1) :=
      fun q => by
        rw [pushToUnit, integral_map (measurable_gaugeFieldRescale a).aemeasurable
          ((hPl1.1 _).1.measurable.aestronglyMeasurable)]
        exact integral_congr_ae (Filter.Eventually.of_forall fun U => (hAct q U).symm)
    rw [hmean p, hmean p']
    exact hUMeans _ (toUnit_mem_unitPositiveClass hC hOne hν) _ _
  · intro β hβ
    obtain ⟨hConv, -, hToErgodic, hToPure⟩ := hPure β hβ
    have hunit : ∀ ν : Measure (GaugeField a),
        IsPeriodicGibbs β ν → pushToUnit ν ∈ periodicGibbsUnit β := fun ν h =>
      (hPG β hβ ν).1 h
    refine ⟨fun ν₁ ν₂ h₁ h₂ t h0 h1 => ?_, fun ν hν => ?_, fun hT ν hν hE => ?_⟩
    · refine (hPG β hβ _).2 ?_
      rw [pushToUnit_add_smul]
      exact hConv _ (hunit _ h₁) _ (hunit _ h₂) t h0 h1
    · have hp := (isExtremalUnitPeriodicGibbs_iff β _).2 ((hPu β hβ ν.1).1 hν)
      obtain ⟨-, h₂, h₃⟩ := hToErgodic _ hp
      exact ((hI.2.2.2 ν).2.1).2 ⟨h₂, h₃⟩
    · have hE' := ((hI.2.2.2 ν).2.1).1 hE
      have hTI : ∀ ν' ∈ periodicGibbsUnit β, IsShiftInvariant ν' := fun ν' h' => by
        obtain ⟨ρ, rfl⟩ := pushToUnit_surjective hS ν'
        have hρ := (hPG β hβ ρ).2 h'
        have hprob : IsProbabilityMeasure ρ := hρ.1.1
        exact ((hC ⟨ρ, hprob⟩).2.1).1 (hT ρ hρ)
      have := hToPure hTI _ (hunit _ hν) ⟨(GibbsAtFixedSpacing.BorelProb.toUnit ν).2, hE'.1, hE'.2⟩
      exact (hPu β hβ ν.1).2 ((isExtremalUnitPeriodicGibbs_iff β _).1 this)
end YangMills.Construction.InfiniteLattice.PeriodicGibbsAtEverySpacing
end
