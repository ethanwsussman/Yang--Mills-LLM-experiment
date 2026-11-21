import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacingProof
import YangMills.Construction.ReflectionPositivity.SitePicturesOfADirection
import YangMills.Construction.ReflectionPositivity.ZeroEnergyAndInvariantObservables
import YangMills.Construction.ReflectionPositivity.ZeroEnergyIsTheInvariantFieldAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
namespace MeshGroundStates
open YangMills.Construction.InfiniteLattice (GaugeField LatticePoint IsBoundedObservable
  IsLocalObservable LatticeSymmetry regionObservables closedHalfSpace halfSpaceLocalObservables
  axisStep shift shiftInvariantSigma condExpShiftInvariant axisShiftInvariantSigma
  IsAxisShiftInvariantSet condExpGiven plateauPairing inverseScaling gaugeFieldRescale
  gaugeFieldUnrescale pullToUnit pushToUnit)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet
  coordinateReflect)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling (TransportsObservables
  TransportsMeasuresAndSymmetries TransportsInvariantSets TransportsStateClass)
variable {a : ℝ}
private theorem actOn_congr {r s : LatticeSymmetry a} (h : r.toFun = s.toFun)
    (F : _root_.YangMills.Construction.InfiniteLattice.GaugeField a → ℂ) : r.actOn F = s.actOn F := by
  have hrs : r = s := by
    cases r
    cases s
    cases h
    rfl
  rw [hrs]
private theorem inverseScaling_image_closedHalfSpace (ha : 0 < a) (μ : Fin 4) :
    inverseScaling ha '' closedHalfSpace μ = closedHalfSpace μ := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.inverseScaling_image_closedHalfSpace <;> assumption
private theorem unrescale_rescale (ha : 0 < a) (h : TransportsObservables ha)
    (U : _root_.YangMills.Construction.InfiniteLattice.GaugeField a) :
    gaugeFieldUnrescale ha (gaugeFieldRescale a U) = U := by
  obtain ⟨e, he, hs⟩ := h.1
  rw [← hs, ← he]
  exact e.symm_apply_apply U
private theorem rescale_injective (ha : 0 < a) (h : TransportsObservables ha) :
    Function.Injective (gaugeFieldRescale a) :=
  Function.LeftInverse.injective (unrescale_rescale ha h)
private theorem measurableSet_rescale_image (ha : 0 < a) (h : TransportsObservables ha)
    {I : Set (_root_.YangMills.Construction.InfiniteLattice.GaugeField a)} (hI : MeasurableSet I) :
    MeasurableSet (gaugeFieldRescale a '' I) := by
  obtain ⟨e, he, -⟩ := h.1
  rw [← he]
  exact e.measurableEmbedding.measurableSet_image.mpr hI
private theorem ae_of_pushToUnit {ν : Measure (_root_.YangMills.Construction.InfiniteLattice.GaugeField a)} {p : _root_.YangMills.Construction.InfiniteLattice.GaugeField 1 → Prop}
    (h : ∀ᵐ U' ∂(_root_.YangMills.Construction.InfiniteLattice.pushToUnit ν), p U') : ∀ᵐ U ∂ν, p (gaugeFieldRescale a U) :=
  ae_of_ae_map (InfiniteLattice.continuous_gaugeFieldRescale a).measurable.aemeasurable h
private theorem ae_eq_of_pullToUnit (ha : 0 < a) (h : TransportsObservables ha)
    {ν : Measure (_root_.YangMills.Construction.InfiniteLattice.GaugeField a)} {f g : _root_.YangMills.Construction.InfiniteLattice.GaugeField a → ℂ}
    (hfg : pullToUnit ha f =ᵐ[_root_.YangMills.Construction.InfiniteLattice.pushToUnit ν] pullToUnit ha g) : f =ᵐ[ν] g := by
  filter_upwards [ae_of_pushToUnit hfg] with U hU
  simpa [pullToUnit, Function.comp_apply, unrescale_rescale ha h U] using hU
private theorem measurable_comp_rescale (ha : 0 < a) (h : TransportsObservables ha)
    (hI : TransportsInvariantSets ha) {g : _root_.YangMills.Construction.InfiniteLattice.GaugeField 1 → ℂ}
    (hg : Measurable[shiftInvariantSigma 1] g) :
    Measurable[shiftInvariantSigma a] (g ∘ gaugeFieldRescale a) := by
  intro Z hZ
  obtain ⟨I, hI₁, hI₂⟩ := hI.2.1 (g ⁻¹' Z) (hg hZ)
  have : (g ∘ gaugeFieldRescale a) ⁻¹' Z = I := by
    rw [Set.preimage_comp, ← hI₂, Set.preimage_image_eq _ (rescale_injective ha h)]
  rw [this]
  exact hI₁
private theorem axisInvariant_rescale_image (ha : 0 < a) (h : TransportsObservables ha)
    (hI : TransportsInvariantSets ha) (μ : Fin 4) {I : Set (_root_.YangMills.Construction.InfiniteLattice.GaugeField a)}
    (hI' : MeasurableSet[axisStepInvariantSigma a μ] I) :
    MeasurableSet[axisShiftInvariantSigma μ] (gaugeFieldRescale a '' I) :=
  ⟨measurableSet_rescale_image ha h hI'.1, (hI.2.2.1 μ I hI'.1).mp hI'.2⟩
private theorem measurable_pullToUnit_of_invariant (ha : 0 < a) (h : TransportsObservables ha)
    (hI : TransportsInvariantSets ha) (μ : Fin 4) {f : _root_.YangMills.Construction.InfiniteLattice.GaugeField a → ℂ}
    (hf : IsBoundedObservable f) (hτ : (shift (axisStep a μ)).actOn f = f) :
    Measurable[axisShiftInvariantSigma μ] (pullToUnit ha f) := by
  intro Z hZ
  have hset : MeasurableSet[axisStepInvariantSigma a μ] (f ⁻¹' Z) := by
    refine ⟨hf.1 hZ, ((shift (axisStep a μ)).actOn_indicator_eq_iff _).mpr ?_⟩
    ext U
    change f ((shift (axisStep a μ)).pullbackField U) ∈ Z ↔ f U ∈ Z
    rw [show f ((shift (axisStep a μ)).pullbackField U) =
      (shift (axisStep a μ)).actOn f U from rfl, hτ]
  have himage : pullToUnit ha f ⁻¹' Z = gaugeFieldRescale a '' (f ⁻¹' Z) := by
    obtain ⟨e, he, hs⟩ := h.1
    ext U'
    constructor
    · intro hU'
      refine ⟨gaugeFieldUnrescale ha U', hU', ?_⟩
      rw [← hs, ← he]
      exact e.apply_symm_apply U'
    · rintro ⟨U, hU, rfl⟩
      change f (gaugeFieldUnrescale ha (gaugeFieldRescale a U)) ∈ Z
      rw [unrescale_rescale ha h]
      exact hU
  rw [himage]
  exact axisInvariant_rescale_image ha h hI μ hset
end MeshGroundStates
open MeshGroundStates in
open YangMills.Construction.InfiniteLattice (IsBoundedObservable IsLocalObservable
  regionObservables closedHalfSpace halfSpaceLocalObservables axisStep gaugeFieldRescale pullToUnit) in
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet
  coordinateReflect) in
theorem groundStatesShiftInvariantAtMesh_holds
    (h₁ : YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (h₂ : SiteReflectionPair.Conclusion)
    (h₃ : GroundStateAndInvariance)
    (h₄ : YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.LatticeFrameAtSpacing)
    (h₅ : YangMills.Construction.ReflectionPositivity.HalfAndShift.HalfAndShiftStatement) :
    GroundStatesShiftInvariantAtMesh := by
  intro a ha ν hν μ
  obtain ⟨hsp, hmeas, -, hclass, hinv⟩ := h₁ a ha
  have hunitRP : GibbsAtFixedSpacing.BorelProb.toUnit ν ∈ reflectionPositiveSet 1 :=
    ((hclass ν).2.2.2.2).mp hν
  have hmem : _root_.YangMills.Construction.InfiniteLattice.pushToUnit ν.1 ∈ ReflectionPositivity.MirrorHyperplanes.unitPositiveClass := by
    rw [← h₅.2]
    exact ⟨_, hunitRP, rfl⟩
  have hcoe : ((unitRepresentative ν.1 : ReflectionPositivity.MirrorHyperplanes.unitPositiveClass) :
      Measure (_root_.YangMills.Construction.InfiniteLattice.GaugeField (1 : ℝ))) = _root_.YangMills.Construction.InfiniteLattice.pushToUnit ν.1 :=
    coe_unitRepresentative hmem
  let ν₁ : ReflectionPositivity.MirrorHyperplanes.unitPositiveClass := ⟨_root_.YangMills.Construction.InfiniteLattice.pushToUnit ν.1, hmem⟩
  obtain ⟨-, -, -, hzero, -, -⟩ := h₂ (unitRepresentative ν.1) μ 1
  obtain ⟨-, -, hdirJ, hdirI, -⟩ := h₃ ν₁ μ
  have hset := hinv.2.2.2 ν
  have hF_mem : ∀ F : _root_.YangMills.Construction.InfiniteLattice.GaugeField a → ℂ, IsLocalObservable F →
      F ∈ regionObservables a (closedHalfSpace μ) →
      pullToUnit ha F ∈ halfSpaceLocalObservables μ := by
    intro F hl hF
    have := (hsp.2.2.2.2.2.2.2.1 (closedHalfSpace μ)).2
    rw [inverseScaling_image_closedHalfSpace ha μ] at this
    have hm : pullToUnit ha F ∈ pullToUnit ha ''
        {F | F ∈ regionObservables a (closedHalfSpace μ) ∧ IsLocalObservable F} := ⟨F, ⟨hF, hl⟩, rfl⟩
    rw [this] at hm
    exact hm
  have hobs : ∀ F : _root_.YangMills.Construction.InfiniteLattice.GaugeField a → ℂ, IsBoundedObservable F →
      IsBoundedObservable (pullToUnit ha F) :=
    fun F hF => hsp.2.1.mapsTo hF
  refine ⟨fun F H hFl hF hHl hH => ?_, fun F' hF' v => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · have hpl := (hset.2.2 hν.1 F H hF.1 hH.1).2
    have hz := hzero.1 (pullToUnit ha F) (hF_mem F hFl hF) (pullToUnit ha H) (hF_mem H hHl hH)
    rw [hcoe] at hz
    exact hz.trans hpl.symm
  · have e₁ := (hset.2.2 hν.1 ((coordinateReflect a μ).actOn F') F'
      (InfiniteLattice.IsBoundedObservable.actOn hF' _) hF').1
    have e₂ := (hset.2.2 hν.1 F' F' hF' hF').1
    have hcomm : pullToUnit ha ((coordinateReflect a μ).actOn F') =
        (ReflectionPositivity.MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F') := by
      rw [hmeas.2.2.1 (coordinateReflect a μ) F' hF']
      exact actOn_congr (((hmeas.2.2.2.2.2.1 μ)).trans
        (ReflectionPositivity.LatticeAtSpacing.coordinateReflect_toFun 1 μ)) _
    have e₃ := (hzero.2 (pullToUnit ha F') (hobs F' hF') 0).1
    rw [hcoe] at e₃
    refine ae_eq_of_pullToUnit ha hsp ?_
    rw [hcomm] at e₁
    exact e₁.trans (e₃.trans e₂.symm)
  · exact ((h₄ a ha).2.2.2.1 ν hν.1 F' F' hF' hF' v).2.2.2.1.symm
  · intro I hI
    exact ⟨hI.1, hI.2 (axisStep a μ)⟩
  · intro I hI
    obtain ⟨I₂, hI₂, hnull⟩ := hdirI _ (axisInvariant_rescale_image ha hsp hinv μ hI)
    obtain ⟨I', hI', rfl⟩ := hinv.2.1 I₂ hI₂
    refine ⟨I', hI', ?_⟩
    have hmI : MeasurableSet (symmDiff I I') :=
      MeasurableSet.symmDiff hI.1 (hI'.1)
    rw [← hset.1 _ hmI, Set.image_symmDiff (rescale_injective ha hsp), symmDiff_comm]
    exact hnull
  · intro J hJ hτ
    have hJm := measurable_pullToUnit_of_invariant ha hsp hinv μ hJ hτ
    have hJo := hobs J hJ
    obtain ⟨C, hC⟩ := hJo.2
    have hprob : IsProbabilityMeasure (ν₁ : Measure (_root_.YangMills.Construction.InfiniteLattice.GaugeField (1 : ℝ))) := ν₁.2.1
    have hLp : MemLp (pullToUnit ha J) 2 (ν₁ : Measure (_root_.YangMills.Construction.InfiniteLattice.GaugeField (1 : ℝ))) :=
      MemLp.of_bound hJo.1.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
    obtain ⟨J₂, hJ₂, heq⟩ := hdirJ _ hJm hLp
    refine ⟨J₂ ∘ gaugeFieldRescale a, measurable_comp_rescale ha hsp hinv hJ₂, ?_⟩
    have heq' : pullToUnit ha J =ᵐ[_root_.YangMills.Construction.InfiniteLattice.pushToUnit ν.1] J₂ := heq
    filter_upwards [ae_of_pushToUnit heq'] with U hU
    simpa [pullToUnit, Function.comp_apply, unrescale_rescale ha hsp U] using hU
end YangMills.Construction.ReflectionPositivity.DirectionPictures
