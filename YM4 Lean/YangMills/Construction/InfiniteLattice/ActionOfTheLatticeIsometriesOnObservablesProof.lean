import YangMills.Construction.ChessboardTori.InvarianceUnderTheGroupsOfGridsProof
import YangMills.Construction.InfiniteLattice.ContinuousLocalFunctionsAreDenseAndTestMeasuresProof
import YangMills.Construction.InfiniteLattice.LatticeIsometriesOfFourSpaceAsBijections
import YangMills.Construction.InfiniteLattice.WilsonMeasureOfAPeriodLatticeAndItsExtensionAreStatesProof
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
namespace YangMills.Construction.InfiniteLattice.SymmetryAction
variable {a : ℝ}
theorem ext_of_toFun_eq {r s : LatticeSymmetry a} (h : r.toFun = s.toFun) : r = s := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem linkMap_linkMap {t r : LatticeSymmetry a} (h : ∀ x, t.toFun (r.toFun x) = x) (b : Link a) :
    t.linkMap (r.linkMap b) = b :=
  Link.ext (Subtype.ext (h b.initial)) (Subtype.ext (h b.terminal))
theorem pullbackField_pullbackField {t r : LatticeSymmetry a}
    (h : ∀ x, t.toFun (r.toFun x) = x) (U : GaugeField a) :
    r.pullbackField (t.pullbackField U) = U :=
  Subtype.ext (funext fun b => congrArg U.1 (linkMap_linkMap h b))
theorem actOn_actOn {t r : LatticeSymmetry a}
    (h : ∀ x, r.toFun (t.toFun x) = x) (F : GaugeField a → ℂ) :
    r.actOn (t.actOn F) = F :=
  funext fun U => congrArg F (pullbackField_pullbackField h U)
theorem actOn_of_forall_fixed {r : LatticeSymmetry a} (h : ∀ x, r.toFun x = x)
    (F : GaugeField a → ℂ) : r.actOn F = F := by apply _root_.YangMills.Construction.ChessboardTori.GridGroupInvariance.actOn_eq_self_of_toFun_eq <;> assumption
theorem imageSet_imageSet {t r : LatticeSymmetry a} (h : ∀ x, t.toFun (r.toFun x) = x)
    (S : Set AmbientSpace) : t.setImage (r.setImage S) = S := by
  simp only [LatticeSymmetry.setImage, image_image, h, image_id']
theorem exists_isInverse (r : LatticeSymmetry a) : ∃ t : LatticeSymmetry a, t.IsInverse r := by
  let e := r.toEquivAmbient
  have hr : ∀ x, r.toFun (e.symm x) = x := fun x => e.apply_symm_apply x
  have hl : ∀ x, e.symm (r.toFun x) = x := fun x => e.symm_apply_apply x
  refine ⟨⟨e.symm, fun x y => ?_, ?_⟩, hl, hr⟩
  · rw [← r.preservesDist, hr, hr]
  · ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : y ∈ r.toFun '' (latticeSubgroup a : Set AmbientSpace) := by
        rw [r.image_eq]
        exact hy
      obtain ⟨z, hz, rfl⟩ := hy'
      rw [hl]
      exact hz
    · intro hx
      refine ⟨r.toFun x, ?_, hl x⟩
      rw [← r.image_eq]
      exact ⟨x, hx, rfl⟩
theorem pullbackField_continuous (r : LatticeSymmetry a) : Continuous r.pullbackField := by apply _root_.YangMills.Construction.InfiniteLattice.LatticeSymmetry.continuous_pullbackField <;> assumption
theorem linkSigma_mono {L L' : Set (Link a)} (h : L ⊆ L') :
    linkSigma L ≤ linkSigma L' :=
  biSup_mono fun _ hb => h hb
theorem measurable_pullbackField (r : LatticeSymmetry a) (L : Set (Link a)) :
    @Measurable _ _ (linkSigma (r.linkMap '' L)) (linkSigma L) r.pullbackField := by
  rw [measurable_iff_comap_le]
  simp only [linkSigma, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  refine iSup₂_le fun b hb => ?_
  exact le_iSup₂_of_le (r.linkMap b) (mem_image_of_mem _ hb) le_rfl
theorem measurable_actOn (r : LatticeSymmetry a) {L : Set (Link a)}
    {F : GaugeField a → ℂ} (hF : @Measurable _ _ (linkSigma L) _ F) :
    @Measurable _ _ (linkSigma (r.linkMap '' L)) _ (r.actOn F) :=
  hF.comp (measurable_pullbackField r L)
theorem actOn_isBoundedObservable (r : LatticeSymmetry a) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) : IsBoundedObservable (r.actOn F) := by apply _root_.YangMills.Construction.InfiniteLattice.LiftedGibbsStates.isBoundedObservable_actOn <;> assumption
theorem linksWithin_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    (linksWithin S : Set (Link a)) ⊆ linksWithin S' :=
  fun _ hb => ⟨h hb.1, h hb.2⟩
theorem image_linksWithin_subset (r : LatticeSymmetry a) (S : Set AmbientSpace) :
    r.linkMap '' (linksWithin S : Set (Link a)) ⊆ linksWithin (r.setImage S) := by
  rintro _ ⟨b, hb, rfl⟩
  exact ⟨⟨_, hb.1, rfl⟩, ⟨_, hb.2, rfl⟩⟩
theorem actOn_mem_regionObservables (r : LatticeSymmetry a) (S : Set AmbientSpace)
    (F : GaugeField a → ℂ) (hF : F ∈ boundedRegionObservables a S) :
    r.actOn F ∈ boundedRegionObservables a (r.setImage S) :=
  ⟨actOn_isBoundedObservable r hF.1,
    Measurable.mono (measurable_actOn r hF.2)
      (linkSigma_mono (image_linksWithin_subset r S)) le_rfl⟩
theorem actOn_image_eq_of_mapsTo (C : Set AmbientSpace → Set (GaugeField a → ℂ))
    (hC : ∀ (r : LatticeSymmetry a) (S : Set AmbientSpace) (F : GaugeField a → ℂ), F ∈ C S →
      r.actOn F ∈ C (r.setImage S))
    (r : LatticeSymmetry a) (S : Set AmbientSpace) :
    (fun F : GaugeField a → ℂ => r.actOn F) '' C S = C (r.setImage S) := by
  obtain ⟨t, hl, hr⟩ := exists_isInverse r
  refine Subset.antisymm ?_ fun G hG => ?_
  · rintro _ ⟨F, hF, rfl⟩
    exact hC r S F hF
  · have h := hC t _ G hG
    rw [imageSet_imageSet hl] at h
    exact ⟨t.actOn G, h, actOn_actOn hr G⟩
theorem boundedRegionObservables_mono {S S' : Set AmbientSpace} (h : S ⊆ S') :
    boundedRegionObservables a S ⊆ boundedRegionObservables a S' :=
  fun _ hF => ⟨hF.1, Measurable.mono hF.2 (linkSigma_mono (linksWithin_mono h)) le_rfl⟩
theorem mem_localRegionObservables {S : Set AmbientSpace} {F : GaugeField a → ℂ} :
    F ∈ localRegionObservables a S ↔
      ∃ Q : Set AmbientSpace, Bornology.IsBounded Q ∧ F ∈ boundedRegionObservables a (S ∩ Q) := by
  simp only [localRegionObservables, mem_iUnion, Set.mem_ofPred_eq, exists_prop]
theorem norm_le_euclidNormVec (z : AmbientSpace) : ‖z‖ ≤ TorusMetric.euclidNormVec z := by apply _root_.YangMills.Construction.InfiniteLattice.ContinuousLocalDensity.norm_le_euclidNormVec <;> assumption
theorem euclidNormVec_le_two_mul_norm (z : AmbientSpace) : TorusMetric.euclidNormVec z ≤ 2 * ‖z‖ := by apply _root_.YangMills.SharedProofs.p8643 <;> assumption
theorem isBounded_imageSet (r : LatticeSymmetry a) {Q : Set AmbientSpace}
    (hQ : Bornology.IsBounded Q) : Bornology.IsBounded (r.setImage Q) := by
  obtain ⟨C, hC⟩ := hQ.exists_norm_le
  refine isBounded_iff_forall_norm_le.2 ⟨2 * C + ‖r.toFun 0‖, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  have h1 := norm_le_euclidNormVec (r.toFun x - r.toFun 0)
  rw [r.preservesDist, sub_zero] at h1
  have h2 := euclidNormVec_le_two_mul_norm x
  have h3 := hC x hx
  linarith [norm_sub_norm_le (r.toFun x) (r.toFun 0)]
theorem actOn_mem_localRegionObservables (r : LatticeSymmetry a) (S : Set AmbientSpace)
    (F : GaugeField a → ℂ) (hF : F ∈ localRegionObservables a S) :
    r.actOn F ∈ localRegionObservables a (r.setImage S) := by
  obtain ⟨Q, hQ, hF⟩ := mem_localRegionObservables.1 hF
  exact mem_localRegionObservables.2 ⟨r.setImage Q, isBounded_imageSet r hQ,
    boundedRegionObservables_mono (image_inter_subset _ _ _)
      (actOn_mem_regionObservables r (S ∩ Q) F hF)⟩
theorem euclidNorm_eq_euclidNormVec (z : AmbientSpace) :
    LatticeConventions.euclidNorm z = TorusMetric.euclidNormVec z := by
  rw [LatticeConventions.euclidNorm, TorusMetric.euclidNormVec, ← Real.sqrt_eq_rpow]
  simp [LatticeConventions.euclidDot, pow_two]
theorem euclidNormVec_initial_sub_terminal (b : Link a) :
    TorusMetric.euclidNormVec ((b.initial : AmbientSpace) - (b.terminal : AmbientSpace)) = |a| := by
  obtain ⟨μ, h | h⟩ := b.isAdjacent
  · have h' : (b.initial : AmbientSpace) - (b.terminal : AmbientSpace)
        = (Pi.single μ (-a) : AmbientSpace) := by
      have h1 : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace)
          = (Pi.single μ a : AmbientSpace) :=
        congrArg Subtype.val h
      rw [Pi.single_neg, ← h1]
      abel
    rw [h', euclidNormVec_single, abs_neg]
  · have h' : (b.initial : AmbientSpace) - (b.terminal : AmbientSpace)
        = (Pi.single μ a : AmbientSpace) := by
      have h1 : (b.terminal : AmbientSpace) - (b.initial : AmbientSpace)
          = -(Pi.single μ a : AmbientSpace) :=
        congrArg Subtype.val h
      rw [← neg_eq_iff_eq_neg.mpr h1]
      abel
    rw [h', euclidNormVec_single]
theorem linksAreNearestNeighbourPairs (ha : 0 < a) : LinksAreNearestNeighbourPairs a := by
  refine ⟨fun x y => ⟨?_, fun h => ?_⟩, fun r b => ⟨r.linkMap b, rfl, rfl⟩⟩
  · rintro ⟨b, rfl, rfl⟩
    rw [euclidNorm_eq_euclidNormVec, euclidNormVec_initial_sub_terminal, abs_of_pos ha]
  · rw [euclidNorm_eq_euclidNormVec] at h
    have h' : TorusMetric.euclidNormVec ((x : AmbientSpace) - (y : AmbientSpace)) = |a| := by
      rw [h, abs_of_pos ha]
    exact ⟨(⟨y, x, isAdjacent_of_euclidNormVec y x h'⟩ : Link a).opposite, rfl, rfl⟩
theorem pullbackFieldIsHomeomorph : PullbackFieldIsHomeomorph a := by
  intro r
  refine ⟨fun U b => U.2 (r.linkMap b), ?_⟩
  obtain ⟨t, hl, hr⟩ := exists_isInverse r
  exact (Homeomorph.mk ⟨r.pullbackField, t.pullbackField,
    pullbackField_pullbackField hr, pullbackField_pullbackField hl⟩
    (pullbackField_continuous r) (pullbackField_continuous t)).isHomeomorph
theorem actOnPreservesAlgebraAndRegions : ActOnPreservesAlgebraAndRegions a := fun r =>
  ⟨fun _ _ hF _ => ⟨actOn_isBoundedObservable r hF, rfl, rfl⟩,
    actOn_image_eq_of_mapsTo (boundedRegionObservables a) actOn_mem_regionObservables r⟩
theorem actOnComp : ActOnComp a :=
  fun _ _ => ⟨rfl, fun _ _ => rfl⟩
theorem shiftActOnRegions : ShiftActOnRegions a := fun v =>
  ⟨actOn_image_eq_of_mapsTo (boundedRegionObservables a) actOn_mem_regionObservables (shift v),
    fun _ _ _ hF => measurable_actOn (shift v) hF⟩
theorem surjective_pullbackField (r : LatticeSymmetry a) :
    Function.Surjective r.pullbackField := by
  obtain ⟨t, hl, _⟩ := exists_isInverse r
  exact fun V => ⟨t.pullbackField V, pullbackField_pullbackField hl V⟩
theorem actOnLinearIsometric : ActOnLinearIsometric a := fun r =>
  ⟨rfl, fun F _ => ⟨fun _ _ => rfl, fun _ => rfl, rfl,
    (surjective_pullbackField r).iSup_comp fun U => ‖F U‖⟩⟩
theorem regionObservablesMonotone : RegionObservablesMonotone a := by
  refine ⟨fun S => ?_, fun S S' h => ⟨boundedRegionObservables_mono h, fun F hF => ?_⟩,
    fun S hS => ?_⟩
  · have h : (linksWithin S : Set (Link a))
        = linksWithin (S ∩ (latticeSubgroup a : Set AmbientSpace)) := by
      ext b
      exact ⟨fun hb => ⟨⟨hb.1, b.initial.2⟩, ⟨hb.2, b.terminal.2⟩⟩,
        fun hb => ⟨hb.1.1, hb.2.1⟩⟩
    exact congrArg linkSigma h
  · obtain ⟨Q, hQ, hF⟩ := mem_localRegionObservables.1 hF
    exact mem_localRegionObservables.2
      ⟨Q, hQ, boundedRegionObservables_mono (inter_subset_inter_left Q h) hF⟩
  · refine Subset.antisymm (fun F hF => mem_localRegionObservables.2 ⟨S, hS, ?_⟩) fun F hF => ?_
    · rwa [inter_self]
    · obtain ⟨Q, _, hF⟩ := mem_localRegionObservables.1 hF
      exact boundedRegionObservables_mono inter_subset_left hF
theorem isStarAlgebra_of_measurableSpace (m : MeasurableSpace (GaugeField a)) :
    IsStarAlgebraOfFunctions
      {F : GaugeField a → ℂ | IsBoundedObservable F ∧ @Measurable _ _ m _ F} := by
  refine ⟨fun c => ⟨⟨measurable_const, ‖c‖, fun _ => le_rfl⟩, measurable_const⟩, ?_, ?_, ?_, ?_⟩
  · rintro F ⟨⟨hm, C, hC⟩, hs⟩ G ⟨⟨hm', D, hD⟩, hs'⟩
    exact ⟨⟨hm.add hm', C + D, fun U =>
      (norm_add_le _ _).trans (add_le_add (hC U) (hD U))⟩, hs.add hs'⟩
  · rintro c F ⟨⟨hm, C, hC⟩, hs⟩
    refine ⟨⟨hm.const_smul c, ‖c‖ * C, fun U => ?_⟩, hs.const_smul c⟩
    rw [Pi.smul_apply, norm_smul]
    exact mul_le_mul_of_nonneg_left (hC U) (norm_nonneg _)
  · rintro F ⟨⟨hm, C, hC⟩, hs⟩ G ⟨⟨hm', D, hD⟩, hs'⟩
    refine ⟨⟨hm.mul hm', C * D, fun U => ?_⟩, hs.mul hs'⟩
    rw [Pi.mul_apply, norm_mul]
    exact mul_le_mul (hC U) (hD U) (norm_nonneg _) ((norm_nonneg _).trans (hC U))
  · rintro F ⟨⟨hm, C, hC⟩, hs⟩
    refine ⟨⟨Complex.continuous_conj.measurable.comp hm, C, fun U => ?_⟩,
      Complex.continuous_conj.measurable.comp hs⟩
    simpa [LatticeConventions.conjFun] using hC U
theorem isStarAlgebra_regionObservables (S : Set AmbientSpace) :
    IsStarAlgebraOfFunctions (boundedRegionObservables a S) :=
  isStarAlgebra_of_measurableSpace (regionSigma S)
theorem exists_isBounded_common {S : Set AmbientSpace} {F G : GaugeField a → ℂ}
    (hF : F ∈ localRegionObservables a S) (hG : G ∈ localRegionObservables a S) :
    ∃ Q : Set AmbientSpace, Bornology.IsBounded Q ∧
      F ∈ boundedRegionObservables a (S ∩ Q) ∧ G ∈ boundedRegionObservables a (S ∩ Q) := by
  obtain ⟨Q, hQ, hF⟩ := mem_localRegionObservables.1 hF
  obtain ⟨Q', hQ', hG⟩ := mem_localRegionObservables.1 hG
  exact ⟨Q ∪ Q', hQ.union hQ',
    boundedRegionObservables_mono (inter_subset_inter_right S subset_union_left) hF,
    boundedRegionObservables_mono (inter_subset_inter_right S subset_union_right) hG⟩
theorem isStarAlgebra_localRegionObservables (S : Set AmbientSpace) :
    IsStarAlgebraOfFunctions (localRegionObservables a S) := by
  refine ⟨fun c => mem_localRegionObservables.2
      ⟨∅, Bornology.isBounded_empty, (isStarAlgebra_regionObservables _).1 c⟩, ?_, ?_, ?_, ?_⟩
  · intro F hF G hG
    obtain ⟨Q, hQ, hF, hG⟩ := exists_isBounded_common hF hG
    exact mem_localRegionObservables.2
      ⟨Q, hQ, (isStarAlgebra_regionObservables _).2.1 F hF G hG⟩
  · intro c F hF
    obtain ⟨Q, hQ, hF⟩ := mem_localRegionObservables.1 hF
    exact mem_localRegionObservables.2
      ⟨Q, hQ, (isStarAlgebra_regionObservables _).2.2.1 c F hF⟩
  · intro F hF G hG
    obtain ⟨Q, hQ, hF, hG⟩ := exists_isBounded_common hF hG
    exact mem_localRegionObservables.2
      ⟨Q, hQ, (isStarAlgebra_regionObservables _).2.2.2.1 F hF G hG⟩
  · intro F hF
    obtain ⟨Q, hQ, hF⟩ := mem_localRegionObservables.1 hF
    exact mem_localRegionObservables.2
      ⟨Q, hQ, (isStarAlgebra_regionObservables _).2.2.2.2 F hF⟩
theorem actOnLocalRegions : ActOnLocalRegions a :=
  ⟨actOn_image_eq_of_mapsTo (localRegionObservables a) actOn_mem_localRegionObservables,
    fun v => actOn_image_eq_of_mapsTo (localRegionObservables a)
      actOn_mem_localRegionObservables (shift v)⟩
theorem isSymmetricUnder_of_isInverse {ν : Measure (GaugeField a)}
    {t r : LatticeSymmetry a} (hrt : t.IsInverse r) (h : IsSymmetricUnder ν r) :
    IsSymmetricUnder ν t := by
  intro A hA
  have h1 := h (t.actOn A) (actOn_isBoundedObservable t hA)
  rw [← h1, actOn_actOn hrt.2 A]
theorem latticeSymmetryInverses : LatticeSymmetryInverses a := fun r =>
  ⟨r.toFun_bijective, exists_isInverse r, fun _ ht =>
    ⟨fun F _ => ⟨actOn_actOn ht.1 F, (actOn_actOn ht.2 F).symm⟩,
      fun _ _ h => isSymmetricUnder_of_isInverse ht h⟩⟩
theorem isSymmetricUnder_comp {ν : Measure (GaugeField a)} {r r' : LatticeSymmetry a}
    (h : IsSymmetricUnder ν r) (h' : IsSymmetricUnder ν r') : IsSymmetricUnder ν (r.comp r') :=
  fun A hA => (h _ (actOn_isBoundedObservable r' hA)).trans (h' A hA)
theorem symmetricUnderCompAndMultiples : SymmetricUnderCompAndMultiples a := by
  intro ν _
  refine ⟨fun _ _ h h' => isSymmetricUnder_comp h h', fun v hv n => ?_⟩
  let H : AddSubgroup (LatticePoint a) :=
    { carrier := {w | IsSymmetricUnder ν (shift w)}
      add_mem' := by
        intro w w' hw hw'
        have h : shift (w + w') = (shift w).comp (shift w') :=
          ext_of_toFun_eq (funext fun x => by
            change x + ((w : AmbientSpace) + (w' : AmbientSpace))
              = x + (w' : AmbientSpace) + (w : AmbientSpace)
            abel)
        change IsSymmetricUnder ν (shift (w + w'))
        rw [h]
        exact isSymmetricUnder_comp hw hw'
      zero_mem' := by
        intro A _
        rw [actOn_of_forall_fixed fun x => by
          change x + (0 : AmbientSpace) = x
          simp]
      neg_mem' := by
        intro w hw
        refine isSymmetricUnder_of_isInverse (r := shift w) ⟨fun x => ?_, fun x => ?_⟩ hw
        · change x + (w : AmbientSpace) + -(w : AmbientSpace) = x
          abel
        · change x + -(w : AmbientSpace) + (w : AmbientSpace) = x
          abel }
  exact H.zsmul_mem hv n
theorem symmetryActionOnObservables : SymmetryActionOnObservables := fun a =>
  ⟨linksAreNearestNeighbourPairs a.2, pullbackFieldIsHomeomorph, actOnPreservesAlgebraAndRegions,
    actOnComp, shiftActOnRegions, actOnLinearIsometric, regionObservablesMonotone,
    fun S => ⟨isStarAlgebra_regionObservables S, isStarAlgebra_localRegionObservables S⟩,
    actOnLocalRegions, latticeSymmetryInverses, symmetricUnderCompAndMultiples⟩
end YangMills.Construction.InfiniteLattice.SymmetryAction
