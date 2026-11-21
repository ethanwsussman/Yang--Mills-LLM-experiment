import YangMills.Construction.InfiniteLattice.DilationCarriesStatesToSpacingOneProof
import YangMills.Construction.InfiniteLattice.EquilibriumClassIsTheSetOfGibbsStatesProof
import YangMills.Construction.ReflectionPositivity.DilationOnOneLattice
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
open InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry IsBoundedObservable
  IsLocalObservable regionObservables observableSupNorm shift axisStep IsSymmetricUnder
  IsShiftInvariant IsPeriodicMeasure IsShiftInvariantSet shiftInvariantSigma
  unitShiftInvariantSigma condExpShiftInvariant plateauPairing scaledCube inverseScaling
  gaugeFieldRescale gaugeFieldUnrescale pullToUnit pointToUnit pointOfUnit conjByScaling
  gaugeFieldEquivUnit IsRegionMeasurable regionSigma linkSigma)
open GibbsAtFixedSpacing (BorelProb boundedMeasurableIn)
open GibbsAtFixedSpacing.ScalingToUnitSpacing
  (TransportsFieldsObservablesMeasures TransportsSymmetriesAndMirrors
    TransportsInvarianceAndErgodicity TransportsGibbsMeasures)
open ReflectionPositivity.MirrorHyperplanes (MirrorPair UnitMirrorPair IsMirrorPlaneOf
  IsDiagonalDirection IsReflectionPositiveAcross basisVec latticeSymmetry_ext)
open ReflectionPositivity.DirectionPictures (axisReflectionGroup cubeOfRadius)
variable {a : ℝ}
theorem gaugeFieldUnrescale_rescale (ha : 0 < a) (U : GaugeField a) :
    gaugeFieldUnrescale ha (gaugeFieldRescale a U) = U :=
  (gaugeFieldEquivUnit ha).left_inv U
theorem gaugeFieldRescale_unrescale (ha : 0 < a) (V : GaugeField 1) :
    gaugeFieldRescale a (gaugeFieldUnrescale ha V) = V :=
  (gaugeFieldEquivUnit ha).right_inv V
theorem continuous_gaugeFieldUnrescale (ha : 0 < a) : Continuous (gaugeFieldUnrescale ha) := by apply _root_.YangMills.Construction.GibbsAtFixedSpacing.ScalingToUnitSpacing.continuous_gaugeFieldUnrescale <;> assumption
def rescaleHomeomorph (ha : 0 < a) : GaugeField a ≃ₜ GaugeField 1 where
  toEquiv := gaugeFieldEquivUnit ha
  continuous_toFun := InfiniteLattice.continuous_gaugeFieldRescale a
  continuous_invFun := continuous_gaugeFieldUnrescale ha
theorem measurableEmbedding_gaugeFieldRescale (ha : 0 < a) :
    MeasurableEmbedding (gaugeFieldRescale a) :=
  (rescaleHomeomorph ha).toMeasurableEquiv.measurableEmbedding
theorem mem_rescale_image_iff (ha : 0 < a) (I : Set (GaugeField a)) (V : GaugeField 1) :
    V ∈ gaugeFieldRescale a '' I ↔ gaugeFieldUnrescale ha V ∈ I := by
  constructor
  · rintro ⟨U, hU, rfl⟩
    rwa [gaugeFieldUnrescale_rescale]
  · exact fun h => ⟨_, h, gaugeFieldRescale_unrescale ha V⟩
theorem measurableSet_rescale_image (ha : 0 < a) {I : Set (GaugeField a)} (hI : MeasurableSet I) :
    MeasurableSet (gaugeFieldRescale a '' I) :=
  (measurableEmbedding_gaugeFieldRescale ha).measurableSet_image' hI
theorem pullToUnit_injective (ha : 0 < a) {E : Type*} :
    Function.Injective (pullToUnit (E := E) ha) := by
  intro F G h
  funext U
  have := congrFun h (gaugeFieldRescale a U)
  simpa only [pullToUnit, Function.comp, gaugeFieldUnrescale_rescale] using this
theorem pullToUnit_comp_rescale (ha : 0 < a) {E : Type*} (F : GaugeField a → E) :
    pullToUnit ha F ∘ gaugeFieldRescale a = F := by
  funext U
  simp only [pullToUnit, Function.comp, gaugeFieldUnrescale_rescale]
theorem pullToUnit_indicator (ha : 0 < a) (I : Set (GaugeField a)) :
    pullToUnit ha (I.indicator (1 : GaugeField a → ℂ)) =
      (gaugeFieldRescale a '' I).indicator 1 := by
  funext V
  by_cases h : gaugeFieldUnrescale ha V ∈ I
  · simp [pullToUnit, Set.indicator, h, (mem_rescale_image_iff ha I V).2 h]
  · have h' : V ∉ gaugeFieldRescale a '' I := fun h' => h ((mem_rescale_image_iff ha I V).1 h')
    simp only [pullToUnit, Function.comp, Set.indicator_of_notMem h, Set.indicator_of_notMem h']
theorem isBoundedObservable_indicator {I : Set (GaugeField a)} (hI : MeasurableSet I) :
    IsBoundedObservable (I.indicator (1 : GaugeField a → ℂ)) := by apply _root_.YangMills.Construction.InfiniteLattice.GibbsCharacterization.isBoundedObservable_indicator <;> assumption
theorem continuous_linkValue (b : InfiniteLattice.Link a) :
    Continuous fun U : GaugeField a => U b := by apply _root_.YangMills.Construction.ReflectionPositivity.RepresentativeCovariance.continuous_eval_link <;> assumption
theorem regionSigma_le (S : Set AmbientSpace) :
    (regionSigma S : MeasurableSpace (GaugeField a)) ≤
      (inferInstance : MeasurableSpace (GaugeField a)) := iSup₂_le fun b _ => Measurable.comap_le (continuous_linkValue b).measurable
theorem regionObservables_eq_boundedMeasurableIn (a : ℝ) (S : Set AmbientSpace) :
    regionObservables a S = boundedMeasurableIn a S := by
  ext F
  constructor
  · rintro ⟨⟨-, hb⟩, hm⟩
    exact ⟨hm, hb⟩
  · rintro ⟨hm, hb⟩
    exact ⟨⟨hm.mono (regionSigma_le S) le_rfl, hb⟩, hm⟩
theorem pullToUnit_image_regionObservables {ha : 0 < a}
    (hS : TransportsFieldsObservablesMeasures ha) (S : Set AmbientSpace) :
    pullToUnit ha '' regionObservables a S = regionObservables 1 (inverseScaling ha '' S) := by
  rw [regionObservables_eq_boundedMeasurableIn, regionObservables_eq_boundedMeasurableIn]
  exact (hS.2.2.2.2.2.2.1 S).1
theorem mem_regionObservables_iff_pullToUnit {ha : 0 < a}
    (hS : TransportsFieldsObservablesMeasures ha) (S : Set AmbientSpace) (F : GaugeField a → ℂ) :
    F ∈ regionObservables a S ↔ pullToUnit ha F ∈ regionObservables 1 (inverseScaling ha '' S) := by
  rw [← pullToUnit_image_regionObservables hS]
  exact (pullToUnit_injective ha).mem_set_image.symm
theorem isBounded_image_inverseScaling (ha : 0 < a) {Q : Set AmbientSpace}
    (hQ : Bornology.IsBounded Q) : Bornology.IsBounded (inverseScaling ha '' Q) :=
  hQ.smul₀ a⁻¹
theorem isBounded_image_inverseScaling_symm (ha : 0 < a) {Q : Set AmbientSpace}
    (hQ : Bornology.IsBounded Q) : Bornology.IsBounded ((inverseScaling ha).symm '' Q) :=
  hQ.smul₀ a
theorem isLocalObservable_iff_pullToUnit {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    IsLocalObservable F ↔ IsLocalObservable (pullToUnit ha F) := by
  constructor
  · rintro ⟨Q, hQ, hm⟩
    exact ⟨inverseScaling ha '' Q, isBounded_image_inverseScaling ha hQ,
      ((mem_regionObservables_iff_pullToUnit hS Q F).1 ⟨hF, hm⟩).2⟩
  · rintro ⟨Q', hQ', hm⟩
    have hobs : IsBoundedObservable (pullToUnit ha F) := hS.2.1.mapsTo hF
    have hQ : inverseScaling ha '' ((inverseScaling ha).symm '' Q') = Q' := by
      rw [image_image]
      simp
    refine ⟨(inverseScaling ha).symm '' Q', isBounded_image_inverseScaling_symm ha hQ', ?_⟩
    refine ((mem_regionObservables_iff_pullToUnit hS _ F).2 ?_).2
    rw [hQ]
    exact ⟨hobs, hm⟩
theorem pullToUnit_image_local {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha)
    (S : Set AmbientSpace) :
    pullToUnit ha '' {F | F ∈ regionObservables a S ∧ IsLocalObservable F} =
      {F' | F' ∈ regionObservables 1 (inverseScaling ha '' S) ∧ IsLocalObservable F'} := by
  ext F'
  constructor
  · rintro ⟨F, ⟨h₁, h₂⟩, rfl⟩
    exact ⟨(mem_regionObservables_iff_pullToUnit hS S F).1 h₁,
      (isLocalObservable_iff_pullToUnit hS h₁.1).1 h₂⟩
  · rintro ⟨h₁, h₂⟩
    rw [← pullToUnit_image_regionObservables hS] at h₁
    obtain ⟨F, hF, rfl⟩ := h₁
    exact ⟨F, ⟨hF, (isLocalObservable_iff_pullToUnit hS hF.1).2 h₂⟩, rfl⟩
theorem inverseScaling_image_centeredCube (ha : 0 < a) (r : ℕ+) :
    inverseScaling ha '' scaledCube a r = cubeOfRadius r := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    obtain ⟨h₁, h₂⟩ := (InfiniteLattice.mem_centeredCube ha r y).1 hy i
    have hi : 0 < a⁻¹ := inv_pos.mpr ha
    have hc : a⁻¹ * ((r : ℝ) * a) = r := by field_simp
    have e : (inverseScaling ha y) i = a⁻¹ * y i := rfl
    rw [e]
    constructor
    · have := mul_le_mul_of_nonneg_left h₁ hi.le
      rw [mul_neg, hc] at this
      exact_mod_cast this
    · have := mul_le_mul_of_nonneg_left h₂ hi.le
      rw [hc] at this
      exact_mod_cast this
  · intro hx
    refine ⟨a • x, (InfiniteLattice.mem_centeredCube ha r _).2 fun i => ?_, ?_⟩
    · obtain ⟨h₁, h₂⟩ := hx i
      have e : (a • x) i = a * x i := rfl
      rw [e]
      constructor <;> nlinarith
    · exact (inverseScaling ha).apply_symm_apply x
theorem transportsObservables {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha) :
    TransportsObservables ha := by
  refine ⟨⟨rescaleHomeomorph ha, rfl, rfl⟩, hS.2.1, fun F _ => pullToUnit_comp_rescale ha F,
    fun F' hF' => ?_, hS.2.2.1, hS.2.2.2.1, fun F hF => ⟨rfl, (hS.2.2.2.2.1 F hF).2, ?_⟩,
    fun S => ⟨pullToUnit_image_regionObservables hS S, pullToUnit_image_local hS S⟩, fun r => ?_⟩
  · obtain ⟨F, hF, rfl⟩ := hS.2.1.surjOn hF'
    rw [pullToUnit_comp_rescale]
    exact ⟨hF, rfl⟩
  · exact (rescaleHomeomorph ha).symm.comp_continuous_iff'
  · rw [pullToUnit_image_regionObservables hS, inverseScaling_image_centeredCube]
theorem dotProduct_inverseScaling_symm (ha : 0 < a) (n x : AmbientSpace) :
    n ⬝ᵥ ((inverseScaling ha).symm x) = a * (n ⬝ᵥ x) :=
  dotProduct_smul a n x
theorem inverseScaling_image_hyperplane (ha : 0 < a) (n : AmbientSpace) (t : ℝ) :
    inverseScaling ha '' {x | n ⬝ᵥ x = t} = {x | n ⬝ᵥ x = t / a} := by
  ext x
  rw [Equiv.image_eq_preimage_symm, mem_preimage, mem_ofPred_eq, mem_ofPred_eq,
    dotProduct_inverseScaling_symm, eq_div_iff ha.ne', mul_comm]
theorem inverseScaling_image_upper (ha : 0 < a) (n : AmbientSpace) (t : ℝ) :
    inverseScaling ha '' {x | t ≤ n ⬝ᵥ x} = {x | t / a ≤ n ⬝ᵥ x} := by
  ext x
  rw [Equiv.image_eq_preimage_symm, mem_preimage, mem_ofPred_eq, mem_ofPred_eq,
    dotProduct_inverseScaling_symm, div_le_iff₀' ha]
theorem inverseScaling_image_lower (ha : 0 < a) (n : AmbientSpace) (t : ℝ) :
    inverseScaling ha '' {x | n ⬝ᵥ x ≤ t} = {x | n ⬝ᵥ x ≤ t / a} := by
  ext x
  rw [Equiv.image_eq_preimage_symm, mem_preimage, mem_ofPred_eq, mem_ofPred_eq,
    dotProduct_inverseScaling_symm, le_div_iff₀' ha]
theorem exists_rescaledMirror (ha : 0 < a) (P : MirrorPair a) :
    ∃ P' : UnitMirrorPair, IsRescaledMirror P P' := by
  refine ⟨⟨P.normal, P.height / a, ?_⟩, rfl, rfl⟩
  rcases P.admissible with ⟨hn, q, hq⟩ | ⟨hn, q, hq⟩
  · exact Or.inl ⟨hn, q, by rw [hq]; field_simp⟩
  · exact Or.inr ⟨hn, q, by rw [hq]; field_simp⟩
theorem exists_mirror_of_unit (ha : 0 < a) (P' : UnitMirrorPair) :
    ∃ P : MirrorPair a, IsRescaledMirror P P' := by
  refine ⟨⟨P'.normal, P'.height * a, ?_⟩, rfl, by field_simp⟩
  rcases P'.admissible with ⟨hn, q, hq⟩ | ⟨hn, q, hq⟩
  · exact Or.inl ⟨hn, q, by rw [hq]; ring⟩
  · exact Or.inr ⟨hn, q, by rw [hq]; ring⟩
theorem inverseScaling_image_mirrorHyperplane (ha : 0 < a) {P : MirrorPair a}
    {P' : UnitMirrorPair} (h : IsRescaledMirror P P') :
    inverseScaling ha '' P.hyperplane = P'.hyperplane := by
  change inverseScaling ha '' {x | P.normal ⬝ᵥ x = P.height} = {x | P'.normal ⬝ᵥ x = P'.height}
  rw [h.1, h.2]
  exact inverseScaling_image_hyperplane ha _ _
theorem inverseScaling_image_upperHalf (ha : 0 < a) {P : MirrorPair a} {P' : UnitMirrorPair}
    (h : IsRescaledMirror P P') : inverseScaling ha '' P.upperHalf = P'.upperHalf := by
  change inverseScaling ha '' {x | P.height ≤ P.normal ⬝ᵥ x} = {x | P'.height ≤ P'.normal ⬝ᵥ x}
  rw [h.1, h.2]
  exact inverseScaling_image_upper ha _ _
theorem inverseScaling_image_lowerHalf (ha : 0 < a) {P : MirrorPair a} {P' : UnitMirrorPair}
    (h : IsRescaledMirror P P') : inverseScaling ha '' P.lowerHalf = P'.lowerHalf := by
  change inverseScaling ha '' {x | P.normal ⬝ᵥ x ≤ P.height} = {x | P'.normal ⬝ᵥ x ≤ P'.height}
  rw [h.1, h.2]
  exact inverseScaling_image_lower ha _ _
theorem toUnit_reflect_toFun (ha : 0 < a) {P : MirrorPair a} {P' : UnitMirrorPair}
    (h : IsRescaledMirror P P') : (P.reflect.toUnit ha).toFun = P'.reflect.toFun := by
  have hd := P.normal_dotProduct_self_ne_zero
  funext x
  change a⁻¹ • InfiniteLattice.hyperplaneReflect P.normal P.height (a • x) =
    InfiniteLattice.hyperplaneReflect P'.normal P'.height x
  rw [h.1, h.2]
  simp only [InfiniteLattice.hyperplaneReflect, dotProduct_smul, smul_eq_mul, smul_sub, smul_smul,
    inv_mul_cancel₀ ha.ne', one_smul]
  congr 2
  field_simp
theorem isMirrorPlaneOf_iff_unit (ha : 0 < a) (S : Set AmbientSpace) :
    IsMirrorPlaneOf a S ↔ IsMirrorPlaneOf 1 (inverseScaling ha '' S) := by
  constructor
  · rintro ⟨P, rfl⟩
    obtain ⟨P', h⟩ := exists_rescaledMirror ha P
    exact ⟨P', (inverseScaling_image_mirrorHyperplane ha h).symm⟩
  · rintro ⟨P', hP'⟩
    obtain ⟨P, h⟩ := exists_mirror_of_unit ha P'
    refine ⟨P, (inverseScaling ha).injective.image_injective ?_⟩
    rw [inverseScaling_image_mirrorHyperplane ha h, hP']
theorem transportsMirrors (ha : 0 < a) : TransportsMirrors ha := by
  refine ⟨fun n t _ => ⟨inverseScaling_image_hyperplane ha n t, ?_⟩, exists_mirror_of_unit ha,
    fun P P' h => ⟨inverseScaling_image_mirrorHyperplane ha h, inverseScaling_image_upperHalf ha h,
      inverseScaling_image_lowerHalf ha h, toUnit_reflect_toFun ha h⟩⟩
  rw [← inverseScaling_image_hyperplane ha n t]
  exact isMirrorPlaneOf_iff_unit ha _
theorem toUnit_axisReflectionSymmetry_toFun (ha : 0 < a) (γ : axisReflectionGroup) :
    ((axisReflectionSymmetry a γ).toUnit ha).toFun = (axisReflectionSymmetry 1 γ).toFun := by
  obtain ⟨ε, hε⟩ := ReflectionPositivity.DirectionPictures.exists_signs_of_mem_axisReflectionGroup γ.2
  funext x i
  change a⁻¹ * (γ.1 (a • x) i) = γ.1 x i
  rw [hε, hε]
  change a⁻¹ * (((ε i : ℤ) : ℝ) * (a * x i)) = _
  field_simp
theorem transportsMeasuresAndSymmetries {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha)
    (hI : TransportsSymmetriesAndMirrors ha) : TransportsMeasuresAndSymmetries ha := by
  refine ⟨hI.1, hS.2.2.2.2.2.2.2.1, hI.2.2.1, hI.2.2.2.1, hI.2.2.2.2.1, fun μ => ?_,
    toUnit_axisReflectionSymmetry_toFun ha, fun t => ?_, hS.2.2.2.2.2.2.2.2⟩
  · exact toUnit_reflect_toFun ha (P := coordinateMirror a μ) (P' := coordinateMirror 1 μ)
      ⟨rfl, (zero_div a).symm⟩
  · obtain ⟨r, hr⟩ := hI.2.1 t
    refine ⟨r, latticeSymmetry_ext hr.symm, fun r₂ h => latticeSymmetry_ext ?_⟩
    funext x
    have h₁ : conjByScaling ha r₂.toFun = conjByScaling ha r.toFun := by
      rw [← hr, ← h]
      rfl
    have h₂ := congrFun h₁ (inverseScaling ha x)
    simp only [conjByScaling, Function.comp, Equiv.symm_apply_apply] at h₂
    exact (inverseScaling ha).injective h₂
theorem integral_toUnit (ha : 0 < a) (ν : BorelProb a) (G : GaugeField 1 → ℂ) :
    (BorelProb.toUnit ν).integral G = ν.integral (G ∘ gaugeFieldRescale a) :=
  (measurableEmbedding_gaugeFieldRescale ha).integral_map G
theorem integral_reflection_form {ha : 0 < a} (hI : TransportsSymmetriesAndMirrors ha)
    (ν : BorelProb a) {P : MirrorPair a} {P' : UnitMirrorPair} (h : IsRescaledMirror P P')
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    (BorelProb.toUnit ν).integral (fun V => conj (P'.reflect.actOn (pullToUnit ha F) V) *
        pullToUnit ha F V) =
      ν.integral fun U => conj (P.reflect.actOn F U) * F U := by
  have e : P'.reflect = P.reflect.toUnit ha :=
    latticeSymmetry_ext (toUnit_reflect_toFun ha h).symm
  rw [integral_toUnit ha, e, ← hI.2.2.1 P.reflect F hF]
  congr 1
  funext U
  change conj (pullToUnit ha (P.reflect.actOn F) (gaugeFieldRescale a U)) *
    pullToUnit ha F (gaugeFieldRescale a U) = _
  simp only [pullToUnit, Function.comp, gaugeFieldUnrescale_rescale]
theorem isReflectionNonnegOn_iff_unit {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha)
    (hI : TransportsSymmetriesAndMirrors ha) (ν : BorelProb a) {P : MirrorPair a}
    {P' : UnitMirrorPair} (h : IsRescaledMirror P P') {H H' : Set AmbientSpace}
    (hH : inverseScaling ha '' H = H') :
    IsReflectionNonnegOn ν P H ↔ IsReflectionNonnegOn (BorelProb.toUnit ν) P' H' := by
  subst hH
  constructor
  · intro hp F' hl hm
    rw [← pullToUnit_image_regionObservables hS] at hm
    obtain ⟨F, hF, rfl⟩ := hm
    rw [integral_reflection_form hI ν h hF.1]
    exact hp F ((isLocalObservable_iff_pullToUnit hS hF.1).2 hl) hF
  · intro hp F hl hm
    have := hp (pullToUnit ha F) ((isLocalObservable_iff_pullToUnit hS hm.1).1 hl)
      ((mem_regionObservables_iff_pullToUnit hS H F).1 hm)
    rwa [integral_reflection_form hI ν h hm.1] at this
theorem transportsStateClass {ha : 0 < a} (hS : TransportsFieldsObservablesMeasures ha)
    (hI : TransportsSymmetriesAndMirrors ha) (hE : TransportsInvarianceAndErgodicity ha)
    (hG : TransportsGibbsMeasures a 1) : TransportsStateClass ha := by
  intro ν
  have key : ∀ (P : MirrorPair a) (P' : UnitMirrorPair), IsRescaledMirror P P' →
      (IsReflectionNonnegOn ν P P.upperHalf ↔
        IsReflectionNonnegOn (BorelProb.toUnit ν) P' P'.upperHalf) ∧
      (IsReflectionNonnegOn ν P P.lowerHalf ↔
        IsReflectionNonnegOn (BorelProb.toUnit ν) P' P'.lowerHalf) ∧
      (IsReflectionPositiveAcross ν.1 P ↔ IsReflectionPositiveAcross (BorelProb.toUnit ν).1 P') := by
    intro P P' h
    have hu := isReflectionNonnegOn_iff_unit hS hI ν h (inverseScaling_image_upperHalf ha h)
    have hl := isReflectionNonnegOn_iff_unit hS hI ν h (inverseScaling_image_lowerHalf ha h)
    exact ⟨hu, hl, (isReflectionPositiveAcross_iff ν P).trans
      ((and_congr hu hl).trans (isReflectionPositiveAcross_iff (BorelProb.toUnit ν) P').symm)⟩
  have ht := (hE ν).2.1
  refine ⟨(hE ν).1, ht, (hG ν).2.1, key, ?_⟩
  constructor
  · rintro ⟨h₁, h₂⟩
    refine ⟨ht.1 h₁, fun P' => ?_⟩
    obtain ⟨P, hP⟩ := exists_mirror_of_unit ha P'
    exact (key P P' hP).1.1 (h₂ P)
  · rintro ⟨h₁, h₂⟩
    refine ⟨ht.2 h₁, fun P => ?_⟩
    obtain ⟨P', hP⟩ := exists_rescaledMirror ha P
    exact (key P P' hP).1.2 (h₂ P')
theorem shift_indicator_iff {ha : 0 < a} (hI : TransportsSymmetriesAndMirrors ha)
    (v : LatticePoint a) {I : Set (GaugeField a)} (hm : MeasurableSet I) :
    (shift v).actOn (I.indicator (1 : GaugeField a → ℂ)) = I.indicator 1 ↔
      (shift (pointToUnit ha v)).actOn
          ((gaugeFieldRescale a '' I).indicator (1 : GaugeField 1 → ℂ)) =
        (gaugeFieldRescale a '' I).indicator 1 := by
  have e : shift (pointToUnit ha v) = (shift v).toUnit ha :=
    latticeSymmetry_ext (hI.2.2.2.1 v).symm
  rw [← pullToUnit_indicator ha, e, ← hI.2.2.1 _ _ (isBoundedObservable_indicator hm)]
  exact (pullToUnit_injective ha).eq_iff.symm
theorem measurableSet_shiftInvariant_iff {ha : 0 < a} (hI : TransportsSymmetriesAndMirrors ha)
    {I : Set (GaugeField a)} (hm : MeasurableSet I) :
    MeasurableSet[shiftInvariantSigma a] I ↔
      MeasurableSet[unitShiftInvariantSigma] (gaugeFieldRescale a '' I) := by
  change IsShiftInvariantSet I ↔ IsShiftInvariantSet (gaugeFieldRescale a '' I)
  constructor
  · refine fun h => ⟨measurableSet_rescale_image ha hm, fun w => ?_⟩
    have := (shift_indicator_iff hI (pointOfUnit a w) hm).1 (h.2 _)
    rwa [InfiniteLattice.pointToUnit_pointOfUnit] at this
  · exact fun h => ⟨hm, fun v => (shift_indicator_iff hI v hm).2 (h.2 _)⟩
theorem toUnit_apply_image (ha : 0 < a) (ν : BorelProb a) (X : Set (GaugeField a)) :
    (BorelProb.toUnit ν).1 (gaugeFieldRescale a '' X) = ν.1 X := by
  change ν.1.map (gaugeFieldRescale a) _ = _
  rw [(measurableEmbedding_gaugeFieldRescale ha).map_apply,
    preimage_image_eq X (measurableEmbedding_gaugeFieldRescale ha).injective]
theorem exists_shiftInvariant_preimage {ha : 0 < a} (hI : TransportsSymmetriesAndMirrors ha)
    {I' : Set (GaugeField 1)} (h : MeasurableSet[unitShiftInvariantSigma] I') :
    ∃ I : Set (GaugeField a), MeasurableSet[shiftInvariantSigma a] I ∧
      gaugeFieldRescale a '' I = I' := by
  have hB : MeasurableSet I' := (show IsShiftInvariantSet I' from h).1
  have hsurj : Function.Surjective (gaugeFieldRescale a) :=
    (gaugeFieldEquivUnit ha).surjective
  have hm : MeasurableSet (gaugeFieldRescale a ⁻¹' I') :=
    (InfiniteLattice.continuous_gaugeFieldRescale a).measurable hB
  have himg := image_preimage_eq I' hsurj
  refine ⟨_, (measurableSet_shiftInvariant_iff hI hm).2 ?_, himg⟩
  rw [himg]
  exact h
theorem transportsInvariantSets {ha : 0 < a} (hI : TransportsSymmetriesAndMirrors ha)
    (hE : TransportsInvarianceAndErgodicity ha) (hG : TransportsGibbsMeasures a 1) :
    TransportsInvariantSets ha := by
  refine ⟨fun I hm => measurableSet_shiftInvariant_iff hI hm,
    fun I' h => exists_shiftInvariant_preimage hI h,
    fun μ I hm => ?_, fun ν => ⟨fun X _ => toUnit_apply_image ha ν X, ?_, fun ht A B hA hB => ?_⟩⟩
  · have := shift_indicator_iff hI (axisStep a μ) hm
    rwa [InfiniteLattice.pointToUnit_axisStep] at this
  · have hp := (hG ν).2.1
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨hp.1 h₁, fun I' hI' => ?_⟩
      obtain ⟨I, hJ, rfl⟩ := exists_shiftInvariant_preimage (ha := ha) hI hI'
      rw [toUnit_apply_image ha]
      exact h₂ I hJ
    · rintro ⟨h₁, h₂⟩
      refine ⟨hp.2 h₁, fun I hJ => ?_⟩
      have hB : MeasurableSet I := (show IsShiftInvariantSet I from hJ).1
      have := h₂ _ ((measurableSet_shiftInvariant_iff hI hB).1 hJ)
      rwa [toUnit_apply_image ha] at this
  · have h := (hE ν).2.2.2.2 ht
    exact ⟨h.1 A hA, h.2.1 A B hA hB⟩
theorem unitScalingDictionary_of_unitSpacingTransport
    (h : GibbsAtFixedSpacing.ScalingToUnitSpacing.UnitSpacingTransport) :
    UnitScalingDictionary := by
  intro a ha
  obtain ⟨hS, hI, hE, hG, -⟩ := h a ha
  exact ⟨transportsObservables hS, transportsMeasuresAndSymmetries hS hI, transportsMirrors ha,
    transportsStateClass hS hI hE (hG 1 one_pos), transportsInvariantSets hI hE (hG 1 one_pos)⟩
end YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling
