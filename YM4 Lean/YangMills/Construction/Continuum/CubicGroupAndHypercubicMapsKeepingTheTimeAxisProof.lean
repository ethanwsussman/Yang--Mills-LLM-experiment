import YangMills.Construction.Continuum.CubicGroupAndHypercubicMapsKeepingTheTimeAxis
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction.Continuum.AxisPreservingSymmetries
open InfiniteLattice (AmbientSpace hyperoctahedralLinearGroup)
open LimitConventions
theorem single_timeIdx_eq_mkPoint (r : ℝ) :
    (Pi.single TimeAxis.timeIdx r : AmbientSpace) = mkPoint 0 r := by
  funext μ
  refine Fin.lastCases ?_ (fun i => ?_) μ
  · rw [mkPoint_last]
    exact Pi.single_eq_same _ _
  · rw [mkPoint_castSucc]
    have hne : i.castSucc ≠ TimeAxis.timeIdx := (Fin.castSucc_lt_last i).ne
    exact show (Pi.single TimeAxis.timeIdx r : AmbientSpace) i.castSucc = 0 from by
      simp [hne]
theorem timeBasisVector_eq_mkPoint : timeBasisVector = mkPoint 0 1 := single_timeIdx_eq_mkPoint 1
theorem mkPoint_neg_zero (a : SpaceVec) : mkPoint (-a) 0 = -mkPoint a 0 := by
  simpa using mkPoint_smul (-1) a 0
theorem mkPoint_eq_add_smul (a : SpaceVec) (t : ℝ) :
    mkPoint a t = mkPoint a 0 + t • timeBasisVector := by
  rw [timeBasisVector_eq_mkPoint, ← mkPoint_smul, ← mkPoint_add]
  simp
theorem timeReflection_mkPoint (a : SpaceVec) (t : ℝ) :
    TimeAxis.timeReflection (mkPoint a t) = mkPoint a (-t) := by
  funext μ
  refine Fin.lastCases ?_ (fun i => ?_) μ
  · rw [mkPoint_last]
    change -(mkPoint a t (Fin.last 3)) = -t
    rw [mkPoint_last]
  · rw [mkPoint_castSucc, ← mkPoint_castSucc a t i]
    fin_cases i <;> rfl
def spatialSignedVectors : Set AmbientSpace := (fun a => mkPoint a 0) '' signedSpaceBasis
theorem signedUnitVectors_eq_union :
    InfiniteLattice.signedUnitVectors = spatialSignedVectors ∪ {timeBasisVector, -timeBasisVector} := by
  ext x
  constructor
  · rintro ⟨μ, h⟩
    induction μ using Fin.lastCases with
    | last =>
      rcases h with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    | cast i =>
      have hi : (Pi.single i.castSucc 1 : AmbientSpace) = mkPoint (spaceBasisVec i) 0 :=
        (mkPoint_spaceBasisVec i).symm
      rcases h with h | h
      · exact Or.inl ⟨_, ⟨i, Or.inl rfl⟩, by rw [h, hi]⟩
      · exact Or.inl ⟨_, ⟨i, Or.inr rfl⟩, by
          change mkPoint (-spaceBasisVec i) 0 = x
          rw [h, hi, mkPoint_neg_zero]⟩
  · have hi : ∀ i : Fin 3, mkPoint (spaceBasisVec i) 0 = Pi.single i.castSucc 1 :=
      fun i => mkPoint_spaceBasisVec i
    rintro (⟨a, ⟨i, rfl | rfl⟩, rfl⟩ | h | h)
    · exact ⟨i.castSucc, Or.inl (hi i)⟩
    · refine ⟨i.castSucc, Or.inr ?_⟩
      change mkPoint (-spaceBasisVec i) 0 = _
      rw [mkPoint_neg_zero, hi]
    · exact ⟨TimeAxis.timeIdx, Or.inl h⟩
    · exact ⟨TimeAxis.timeIdx, Or.inr h⟩
theorem timeComponent_of_mem_spatialSignedVectors {x : AmbientSpace} (hx : x ∈ spatialSignedVectors) :
    TimeAxis.timeComponent x = 0 := by
  obtain ⟨a, -, rfl⟩ := hx
  exact timeComponent_mkPoint a 0
theorem timeComponent_timeBasisVector : TimeAxis.timeComponent timeBasisVector = 1 := by
  rw [timeBasisVector_eq_mkPoint, timeComponent_mkPoint]
theorem timeComponent_neg_timeBasisVector : TimeAxis.timeComponent (-timeBasisVector) = -1 := by
  change -TimeAxis.timeComponent timeBasisVector = -1
  rw [timeComponent_timeBasisVector]
theorem ne_zero_of_mem_signedSpaceBasis {a : SpaceVec} (ha : a ∈ signedSpaceBasis) :
    a ≠ 0 := by
  rintro rfl
  obtain ⟨i, h | h⟩ := ha
  · have := congrFun h i
    simp [spaceBasisVec] at this
  · have := congrFun h i
    simp [spaceBasisVec] at this
theorem timeExtension_timeBasisVector (w : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    timeExtension w timeBasisVector = timeBasisVector := by
  rw [timeBasisVector_eq_mkPoint, timeExtension_mkPoint, map_zero]
theorem timeExtension_mem {w : SpaceVec ≃ₗ[ℝ] SpaceVec} (hw : w ∈ octahedralGroup3) :
    timeExtension w ∈ hyperoctahedralLinearGroup := by
  have hw' : w '' signedSpaceBasis = signedSpaceBasis := hw
  change timeExtension w '' InfiniteLattice.signedUnitVectors = InfiniteLattice.signedUnitVectors
  rw [signedUnitVectors_eq_union, image_union, image_pair, map_neg, timeExtension_timeBasisVector]
  congr 1
  rw [spatialSignedVectors, image_image]
  simp only [timeExtension_mkPoint]
  rw [← image_image (fun a => mkPoint a 0) (fun a => w a) signedSpaceBasis]
  exact congrArg _ hw'
theorem timeExtension_mul (w w' : SpaceVec ≃ₗ[ℝ] SpaceVec) :
    timeExtension (w * w') = timeExtension w * timeExtension w' := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, t, rfl⟩ : ∃ a t, x = mkPoint a t := ⟨_, _, (mkPoint_spacePart_timeComponent x).symm⟩
  rw [LinearEquiv.mul_apply, timeExtension_mkPoint, timeExtension_mkPoint, timeExtension_mkPoint,
    LinearEquiv.mul_apply]
theorem timeExtension_one : timeExtension 1 = 1 := by
  refine LinearEquiv.ext fun x => ?_
  obtain ⟨a, t, rfl⟩ : ∃ a t, x = mkPoint a t := ⟨_, _, (mkPoint_spacePart_timeComponent x).symm⟩
  rw [timeExtension_mkPoint]
  rfl
section Preserving
variable {w : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
theorem apply_timeBasisVector (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w) :
    w timeBasisVector = timeBasisVector ∨ w timeBasisVector = -timeBasisVector := by
  have hw' : w '' InfiniteLattice.signedUnitVectors = InfiniteLattice.signedUnitVectors := hw
  have h1 : w timeBasisVector ∈ InfiniteLattice.signedUnitVectors := by
    rw [← hw']
    exact mem_image_of_mem _ ⟨TimeAxis.timeIdx, Or.inl rfl⟩
  have h2 : w timeBasisVector ∈ TimeAxis.timeLine := by
    rw [← show w '' TimeAxis.timeLine = TimeAxis.timeLine from hax]
    exact mem_image_of_mem _ ⟨1, rfl⟩
  obtain ⟨r, hr⟩ := h2
  rw [signedUnitVectors_eq_union] at h1
  rcases h1 with ⟨a, ha, h⟩ | h | h
  · have h3 : mkPoint a 0 = mkPoint 0 r := (h.trans hr.symm).trans (single_timeIdx_eq_mkPoint r)
    exact absurd (mkPoint_inj h3).1 (ne_zero_of_mem_signedSpaceBasis ha)
  · exact Or.inl h
  · exact Or.inr h
theorem apply_mem_spatialSignedVectors (hw : w ∈ hyperoctahedralLinearGroup)
    (hax : PreservesTimeLine w) {x : AmbientSpace}
    (hx : x ∈ spatialSignedVectors) : w x ∈ spatialSignedVectors := by
  have hw' : w '' InfiniteLattice.signedUnitVectors = InfiniteLattice.signedUnitVectors := hw
  have h1 : w x ∈ InfiniteLattice.signedUnitVectors := by
    rw [← hw', signedUnitVectors_eq_union]
    exact mem_image_of_mem _ (Or.inl hx)
  have hE : x ≠ timeBasisVector := fun h => by
    have := timeComponent_of_mem_spatialSignedVectors hx
    rw [h, timeComponent_timeBasisVector] at this
    exact one_ne_zero this
  have hN : x ≠ -timeBasisVector := fun h => by
    have := timeComponent_of_mem_spatialSignedVectors hx
    rw [h, timeComponent_neg_timeBasisVector] at this
    norm_num at this
  rw [signedUnitVectors_eq_union] at h1
  rcases h1 with h | hy | hy
  · exact h
  · rcases apply_timeBasisVector hw hax with h | h
    · exact absurd (w.injective (hy.trans h.symm)) hE
    · exact absurd (w.injective (by rw [hy, map_neg, h, neg_neg])) hN
  · have hy' : w x = -timeBasisVector := hy
    rcases apply_timeBasisVector hw hax with h | h
    · exact absurd (w.injective (by rw [hy', map_neg, h])) hN
    · exact absurd (w.injective (by rw [hy', h])) hE
theorem inv_preserves (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w) :
    w⁻¹ ∈ hyperoctahedralLinearGroup ∧ PreservesTimeLine w⁻¹ := by
  have h : w ∈ timeLineStabilizer := ⟨hw, hax⟩
  exact inv_mem h
theorem apply_inv_self_apply (y : AmbientSpace) : w (w⁻¹ y) = y := by
  rw [← LinearEquiv.mul_apply, mul_inv_cancel]
  rfl
theorem isPurelySpatial_map_mkPoint (hw : w ∈ hyperoctahedralLinearGroup)
    (hax : PreservesTimeLine w) (a : SpaceVec) :
    TimeAxis.IsPurelySpatial (w (mkPoint a 0)) := by
  obtain ⟨π, s, hs⟩ := (InfiniteLattice.mem_hyperoctahedralLinearGroup_iff w).1 hw
  have hne : w timeBasisVector TimeAxis.timeIdx ≠ 0 := by
    rcases apply_timeBasisVector hw hax with h | h
    · rw [h]
      change TimeAxis.timeComponent timeBasisVector ≠ 0
      rw [timeComponent_timeBasisVector]
      exact one_ne_zero
    · rw [h]
      change TimeAxis.timeComponent (-timeBasisVector) ≠ 0
      rw [timeComponent_neg_timeBasisVector]
      norm_num
  have h3 : π TimeAxis.timeIdx = TimeAxis.timeIdx := by
    by_contra hn
    apply hne
    rw [hs, timeBasisVector, Pi.single_eq_of_ne hn, mul_zero]
  change w (mkPoint a 0) TimeAxis.timeIdx = 0
  rw [hs, h3]
  have : mkPoint a 0 TimeAxis.timeIdx = 0 := timeComponent_mkPoint a 0
  rw [this, mul_zero]
theorem map_mkPoint_zero (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w)
    (a : SpaceVec) : w (mkPoint a 0) = mkPoint (spatialRestriction w a) 0 :=
  apply_mkPoint_zero w (isPurelySpatial_map_mkPoint hw hax) a
theorem image_spatialSlice (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w) :
    w '' spatialSlice = spatialSlice := by
  obtain ⟨hi, hia⟩ := inv_preserves hw hax
  ext y
  constructor
  · rintro ⟨_, ⟨a, rfl⟩, rfl⟩
    exact ⟨spatialRestriction w a, (map_mkPoint_zero hw hax a).symm⟩
  · rintro ⟨b, rfl⟩
    refine ⟨mkPoint (spatialRestriction w⁻¹ b) 0, ⟨_, rfl⟩, ?_⟩
    change w (mkPoint (spatialRestriction w⁻¹ b) 0) = mkPoint b 0
    rw [← map_mkPoint_zero hi hia, apply_inv_self_apply]
theorem spatialRestriction_mem_signedSpaceBasis (hw : w ∈ hyperoctahedralLinearGroup)
    (hax : PreservesTimeLine w) {a : SpaceVec} (ha : a ∈ signedSpaceBasis) :
    spatialRestriction w a ∈ signedSpaceBasis := by
  obtain ⟨b, hb, h⟩ :=
    apply_mem_spatialSignedVectors hw hax (mem_image_of_mem (fun a => mkPoint a 0) ha)
  have h' : mkPoint b 0 = mkPoint (spatialRestriction w a) 0 := h.trans (map_mkPoint_zero hw hax a)
  rwa [← (mkPoint_inj h').1]
theorem bijOn_spatialRestriction (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w) :
    BijOn (spatialRestriction w) signedSpaceBasis signedSpaceBasis := by
  obtain ⟨hi, hia⟩ := inv_preserves hw hax
  refine ⟨fun a ha => spatialRestriction_mem_signedSpaceBasis hw hax ha, fun a _ b _ h => ?_,
    fun b hb => ?_⟩
  · have h' : w (mkPoint a 0) = w (mkPoint b 0) := by
      rw [map_mkPoint_zero hw hax, map_mkPoint_zero hw hax]
      exact congrArg (fun c => mkPoint c 0) h
    exact (mkPoint_inj (w.injective h')).1
  · refine ⟨spatialRestriction w⁻¹ b, spatialRestriction_mem_signedSpaceBasis hi hia hb, ?_⟩
    have h : mkPoint (spatialRestriction w (spatialRestriction w⁻¹ b)) 0 = mkPoint b 0 := by
      rw [← map_mkPoint_zero hw hax, ← map_mkPoint_zero hi hia, apply_inv_self_apply]
    exact (mkPoint_inj h).1
theorem map_mkPoint_of_fixes (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w)
    (he : w timeBasisVector = timeBasisVector) (a : SpaceVec) (t : ℝ) :
    w (mkPoint a t) = mkPoint (spatialRestriction w a) t := by
  rw [mkPoint_eq_add_smul a t, map_add, map_smul, he, map_mkPoint_zero hw hax,
    ← mkPoint_eq_add_smul]
theorem map_mkPoint_of_reverses (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w)
    (he : w timeBasisVector = -timeBasisVector) (a : SpaceVec) (t : ℝ) :
    w (mkPoint a t) = mkPoint (spatialRestriction w a) (-t) := by
  rw [mkPoint_eq_add_smul a t, map_add, map_smul, he, map_mkPoint_zero hw hax,
    mkPoint_eq_add_smul (spatialRestriction w a) (-t), neg_smul, smul_neg]
theorem mul_preserves_and_restriction (hw : w ∈ hyperoctahedralLinearGroup)
    (hax : PreservesTimeLine w) {w' : AmbientSpace ≃ₗ[ℝ] AmbientSpace}
    (hw' : w' ∈ hyperoctahedralLinearGroup) (hax' : PreservesTimeLine w') :
    PreservesTimeLine (w * w') ∧
      spatialRestriction (w * w') = spatialRestriction w ∘ₗ spatialRestriction w' := by
  have h : w * w' ∈ timeLineStabilizer :=
    mul_mem (show w ∈ timeLineStabilizer from ⟨hw, hax⟩)
      (show w' ∈ timeLineStabilizer from ⟨hw', hax'⟩)
  refine ⟨h.2, LinearMap.ext fun a => ?_⟩
  change spacePart ((w * w') (mkPoint a 0)) = spacePart (w (mkPoint (spatialRestriction w' a) 0))
  rw [LinearEquiv.mul_apply, map_mkPoint_zero hw' hax']
theorem preservesTimeLineFacts (hw : w ∈ hyperoctahedralLinearGroup) (hax : PreservesTimeLine w) :
    PreservesTimeLineFacts w := by
  obtain ⟨v, hv, hvf⟩ := exists_mem_octahedralGroup3 (spatialRestriction w) (bijOn_spatialRestriction hw hax)
  refine ⟨apply_timeBasisVector hw hax, image_spatialSlice hw hax, map_mkPoint_zero hw hax,
    ⟨v, hv, hvf, fun he => LinearEquiv.ext fun x => ?_, fun he => funext fun x => ?_⟩,
    fun w' hw' hax' => mul_preserves_and_restriction hw hax hw' hax'⟩
  · obtain ⟨a, t, rfl⟩ : ∃ a t, x = mkPoint a t := ⟨_, _, (mkPoint_spacePart_timeComponent x).symm⟩
    rw [map_mkPoint_of_fixes hw hax he, timeExtension_mkPoint, congrFun hvf a]
  · obtain ⟨a, t, rfl⟩ : ∃ a t, x = mkPoint a t := ⟨_, _, (mkPoint_spacePart_timeComponent x).symm⟩
    rw [Function.comp_apply, map_mkPoint_of_reverses hw hax he, timeExtension_mkPoint,
      timeReflection_mkPoint, congrFun hvf a]
theorem preservesTimeLine_of_fixes (he : w timeBasisVector = timeBasisVector) :
    PreservesTimeLine w := by
  have h : ∀ r : ℝ, w (Pi.single TimeAxis.timeIdx r) = Pi.single TimeAxis.timeIdx r := fun r => by
    have hr : (Pi.single TimeAxis.timeIdx r : AmbientSpace) = r • timeBasisVector := by
      rw [single_timeIdx_eq_mkPoint, timeBasisVector_eq_mkPoint, ← mkPoint_smul]
      simp
    rw [hr, map_smul, he]
  ext y
  constructor
  · rintro ⟨_, ⟨r, rfl⟩, rfl⟩
    exact ⟨r, (h r).symm⟩
  · rintro ⟨r, rfl⟩
    exact ⟨_, ⟨r, rfl⟩, h r⟩
end Preserving
theorem classification : Classification := by
  refine ⟨fun w hw => ⟨timeExtension_mem hw, timeExtension_timeBasisVector w⟩,
    fun w _ w' _ => ?_, timeExtension_one, fun w _ => ?_, fun w hw hax => preservesTimeLineFacts hw hax, ?_,
    fun w _ => ?_, fun w => ⟨fun ⟨hw, he⟩ => ?_, ?_⟩,
    fun w hw => ⟨hw.2, preservesTimeLineFacts hw.1 hw.2⟩⟩
  · rw [timeExtension_mul]
    rfl
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← timeExtension_mul, inv_mul_cancel, timeExtension_one]
  · refine LinearMap.ext fun a => ?_
    change spacePart (mkPoint a 0) = a
    rw [spacePart_mkPoint]
  · refine LinearMap.ext fun a => ?_
    change spacePart (timeExtension w (mkPoint a 0)) = w a
    rw [timeExtension_mkPoint, spacePart_mkPoint]
  · have hax := preservesTimeLine_of_fixes he
    obtain ⟨-, -, -, ⟨v, hv, -, h, -⟩, -⟩ := preservesTimeLineFacts hw hax
    exact ⟨v, hv, h he⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨timeExtension_mem hv, timeExtension_timeBasisVector v⟩
end YangMills.Construction.Continuum.AxisPreservingSymmetries
end
