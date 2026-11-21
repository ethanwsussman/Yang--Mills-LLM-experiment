import YangMills.Construction.InfiniteLattice.CoarseStepsAndTheFivePointInequalityProof
import YangMills.Construction.InfiniteLattice.FrameOfTheLatticeAtASpacing
import YangMills.Construction.InfiniteLattice.GibbsStatesByWindowsAndPeriodGroups
import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacing
import YangMills.Construction.ReflectionPositivity.DilationOnOneLattice
import YangMills.Construction.ReflectionPositivity.FunctionsOfTheBondsInASet
import YangMills.Construction.ReflectionPositivity.OneSideAndOneTranslation
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry IsLocalObservable
  IsBoundedObservable closedHalfSpace halfSpaceLocalObservables regionObservables observableSupNorm
  scaledCube inverseScaling pointOfUnit pointToUnit pointToUnit_axisStep axisStep shift pullToUnit
  pushToUnit unitRegionObservables)
open GibbsAtFixedSpacing (BorelProb)
open ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open ReflectionPositivity.LatticeAtSpacing.UnitScaling (TransportsObservables
  TransportsMeasuresAndSymmetries)
open FormHilbert
namespace ScaledClassesProof
variable {a : ℝ}
theorem symmetry_ext {b : ℝ} {r r' : LatticeSymmetry b} (h : r.toFun = r'.toFun) : r = r' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem isBoundedObservable_conj_mul {b : ℝ} {A B : GaugeField b → ℂ} (hA : IsBoundedObservable A)
    (hB : IsBoundedObservable B) : IsBoundedObservable fun U => conj (A U) * B U := by apply _root_.YangMills.Construction.LatticeConventions.CoarseStepFivePoint.isBoundedObservable_conjFun_mul <;> assumption
theorem toUnit_ofUnit (ha : 0 < a) (x : LatticePoint (1 : ℝ)) :
    pointToUnit ha (pointOfUnit a x) = x := by apply _root_.YangMills.Construction.InfiniteLattice.pointToUnit_pointOfUnit <;> assumption
theorem inverseScaling_image_closedHalfSpace (ha : 0 < a) (μ : Fin 4) :
    inverseScaling ha '' closedHalfSpace μ = closedHalfSpace μ := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change 0 ≤ a⁻¹ * y μ
    exact mul_nonneg (inv_pos.mpr ha).le hy
  · intro hx
    refine ⟨a • x, ?_, inv_smul_smul₀ ha.ne' x⟩
    change 0 ≤ a * x μ
    exact mul_nonneg ha.le hx
theorem pushToUnit_mem_unitPositiveClass
    (hD : ReflectionPositivity.LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hS : ReflectionPositivity.HalfAndShift.HalfAndShiftStatement) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) : pushToUnit ν.1 ∈ unitPositiveClass := by
  have h := (((hD a ha).2.2.2.1 ν).2.2.2.2).1 hν
  rw [← show _ = unitPositiveClass from hS.2]
  exact ⟨GibbsAtFixedSpacing.BorelProb.toUnit ν, h, rfl⟩
theorem pullToUnit_shift (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha) (v : LatticePoint a)
    {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((shift v).actOn F) =
      (shift (pointToUnit ha v)).actOn (pullToUnit ha F) := by
  rw [hM.2.2.1 (shift v) F hF, symmetry_ext (hM.2.2.2.1 v)]
theorem pullToUnit_coordinateReflect (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (μ : Fin 4) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((ReflectionPositivity.LatticeAtSpacing.coordinateReflect a μ).actOn F) =
      (ReflectionPositivity.MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F) := by
  rw [hM.2.2.1 _ F hF, symmetry_ext ((hM.2.2.2.2.2.1 μ).trans
    (ReflectionPositivity.LatticeAtSpacing.coordinateReflect_toFun 1 μ))]
theorem integral_reflect_unitRepresentative (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (ν : BorelProb a)
    (hν : (unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ))) = pushToUnit ν.1)
    (μ : Fin 4) {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    ∫ U, conj ((ReflectionPositivity.MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F) U) *
        pullToUnit ha H U ∂(unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ))) =
      ν.integral fun U =>
        conj ((ReflectionPositivity.LatticeAtSpacing.coordinateReflect a μ).actOn F U) * H U := by
  have h := hM.2.1 ν _ (isBoundedObservable_conj_mul
    (hF.actOn (ReflectionPositivity.LatticeAtSpacing.coordinateReflect a μ)) hH)
  rw [← h, hν]
  change _ = ∫ U, conj (pullToUnit ha
    ((ReflectionPositivity.LatticeAtSpacing.coordinateReflect a μ).actOn F) U) *
    pullToUnit ha H U ∂(pushToUnit ν.1)
  rw [pullToUnit_coordinateReflect ha hM μ hF]
theorem isBounded_centeredCube (a : ℝ) (r : ℕ) : Bornology.IsBounded (scaledCube a r) :=
  (isCompact_univ_pi fun _ => isCompact_Icc).isBounded.smul₀ a
theorem shift_centeredCube_subset (ha : 0 < a) (μ : Fin 4) (r : ℕ) :
    (shift (r • axisStep a μ)).setImage (scaledCube a r) ∩
        (InfiniteLattice.latticeSubgroup a : Set AmbientSpace) ⊆
      closedHalfSpace μ := by
  rintro _ ⟨⟨y, hy, rfl⟩, -⟩
  have h := ((InfiniteLattice.mem_centeredCube ha r y).1 hy μ).1
  change 0 ≤ y μ + (r • (Pi.single μ a : AmbientSpace)) μ
  simp only [Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul]
  linarith
end ScaledClassesProof
open ScaledClassesProof in
theorem scaledClassesTheorem_of_unitPicture
    (hD : ReflectionPositivity.LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hP : ReflectionPairTheorem)
    (hFr : ReflectionPositivity.LatticeAtSpacing.LatticeFrameAtSpacing)
    (hB : ReflectionPositivity.RegionFunctions.RegionFunctionsStatement)
    (hS : ReflectionPositivity.HalfAndShift.HalfAndShiftStatement) :
    ScaledClassesTheorem := by
  intro a ha ν hν μ
  obtain ⟨hSp, hM, -, -, -⟩ := hD a ha
  have hcoe := coe_unitRepresentative (pushToUnit_mem_unitPositiveClass hD hS ha hν)
  have hPic := hP (unitRepresentative ν.1) μ ReflectionPair.site
  have hpos := hPic.1.1
  have hsys := hPic.2.1.2.2
  have hobs : ∀ F ∈ halfSpaceLocalAtMesh a μ, IsBoundedObservable F := fun F h => h.1.1
  have hImg : pullToUnit ha '' (halfSpaceLocalAtMesh a μ : Set (GaugeField a → ℂ)) =
      (halfSpaceLocalObservables μ : Set (GaugeField (1 : ℝ) → ℂ)) := by
    have h := (hSp.2.2.2.2.2.2.2.1 (closedHalfSpace μ)).2
    rw [inverseScaling_image_closedHalfSpace ha μ] at h
    exact h
  have hFlat : ∀ F ∈ halfSpaceLocalAtMesh a μ,
      pullToUnit ha F ∈ halfSpaceLocalObservables μ := fun F hF => by
    exact show pullToUnit ha F ∈ (halfSpaceLocalObservables μ : Set (GaugeField (1 : ℝ) → ℂ)) from
      hImg ▸ Set.mem_image_of_mem _ hF
  let L : halfSpaceLocalAtMesh a μ →ₗ[ℂ] halfSpaceLocalObservables μ :=
    { toFun := fun F => ⟨pullToUnit ha F, hFlat F F.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hL : Function.Surjective L := by
    rintro ⟨G, hG⟩
    have hG' : G ∈ pullToUnit ha ''
        (halfSpaceLocalAtMesh a μ : Set (GaugeField a → ℂ)) := hImg.symm ▸ hG
    obtain ⟨F, hF, rfl⟩ := hG'
    exact ⟨⟨F, hF⟩, rfl⟩
  have hcl : ∀ F : halfSpaceLocalAtMesh a μ,
      ScaledPair.obsClass ν.1 μ ha (F : GaugeField a → ℂ) =
        formClass (ReflectionPair.site.pairForm (unitRepresentative ν.1) μ) (L F) := fun F => by
    change ReflectionPair.site.obsClass _ μ (pullToUnit ha F) = _
    rw [ReflectionPair.obsClass, dif_pos (hFlat F F.2)]
    rfl
  have hform : ∀ F H : halfSpaceLocalAtMesh a μ, reflectedFormAtMesh ν μ F H =
      ReflectionPair.site.pairForm (unitRepresentative ν.1) μ (L F) (L H) := fun F H => by
    rw [ReflectionPair.pairForm_apply]
    exact (integral_reflect_unitRepresentative ha hM ν hcoe μ (hobs F F.2) (hobs H H.2)).symm
  have hpf : IsPosSesqForm (reflectedFormAtMesh ν μ) :=
    { sesq :=
        ⟨fun F₁ F₂ F' => by
            simp only [hform, map_add, hpos.sesq.add_left],
          fun c F F' => by
            simp only [hform, map_smul, hpos.sesq.smul_left],
          fun F F₁ F₂ => by
            simp only [hform, map_add, hpos.sesq.add_right],
          fun c F F' => by
            simp only [hform, map_smul, hpos.sesq.smul_right]⟩
      nonneg := fun F => by
        rw [hform]
        exact hpos.nonneg _ }
  refine ⟨⟨hImg, ⟨formClass _ ∘ₗ L, fun F => (hcl F).symm, ?_⟩, fun F hF => ?_⟩,
    ⟨fun F hF H hH n w hw => ?_, fun F hF => ?_, fun F H => ?_, hpf, hpf.isConjSymm⟩,
    fun F hF r A hA γ => ?_⟩
  · rw [LinearMap.coe_comp, hL.range_comp]
    exact show DenseRange ((↑) : FormSeminormed (ReflectionPair.site.pairForm (unitRepresentative ν.1) μ) →
        UniformSpace.Completion
          (FormSeminormed (ReflectionPair.site.pairForm (unitRepresentative ν.1) μ))) from
      UniformSpace.Completion.denseRange_coe
  · have h := hPic.1.2.2 _ (hFlat F hF)
    rwa [(hSp.2.2.2.2.2.2.1 F (hobs F hF)).2.1] at h
  · have h := hPic.2.2.1 _ (hFlat F hF) _ (hFlat H hH) n w hw
    have hfl := pullToUnit_shift ha hM (pointOfUnit a (n • axisStep 1 μ + intPoint w))
      (hobs H hH)
    rw [toUnit_ofUnit] at hfl
    refine h.trans ?_
    rw [← hfl]
    exact integral_reflect_unitRepresentative ha hM ν hcoe μ (hobs F hF) ((hobs H hH).actOn _)
  · refine ⟨?_, fun l => ?_⟩
    · have hfl := pullToUnit_shift ha hM (axisStep a μ) (hobs F hF)
      rw [pointToUnit_axisStep] at hfl
      refine (hsys.1 _ (hFlat F hF)).trans ?_
      rw [← hfl]
      rfl
    · have hfl := pullToUnit_shift ha hM (axisStep a l.1) (hobs F hF)
      rw [pointToUnit_axisStep] at hfl
      refine (hsys.2 l _ (hFlat F hF)).trans ?_
      rw [← hfl]
      rfl
  · rw [hform, hcl F, hcl H]
    exact inner_formClass hpos (L F) (L H)
  · have hAobs : IsBoundedObservable A := hA.1
    have hfl := pullToUnit_shift ha hM ((r : ℕ) • axisStep a μ) hAobs
    rw [map_nsmul, pointToUnit_axisStep] at hfl
    have hAct := (hFr a ha).2.2.1 (shift ((r : ℕ) • axisStep a μ))
      (shift ((r : ℕ) • axisStep a μ))
    have hIn : (shift ((r : ℕ) • axisStep a μ)).actOn A ∈
        regionObservables a ((shift ((r : ℕ) • axisStep a μ)).setImage (scaledCube a r)) :=
      hAct.2.2.2.2.2.2.2.2.1 (scaledCube a r) ▸ Set.mem_image_of_mem _ hA
    refine ⟨⟨(hB a ha _ (closedHalfSpace μ)).2.1.1 (shift_centeredCube_subset ha μ r) hIn,
        hAct.2.2.2.2.2.2.2.2.2.2.2.2 A hAobs ⟨scaledCube a r, isBounded_centeredCube a r, hA.2⟩⟩,
      rfl, rfl, ?_, rfl, ?_, ?_, (hSp.2.2.2.2.2.2.1 A hAobs).1⟩
    · change ReflectionPair.site.obsClass _ μ (pullToUnit ha _) = _
      rw [hfl]
    · have h : pullToUnit ha A ∈ regionObservables 1 (cubeOfRadius r) :=
        hSp.2.2.2.2.2.2.2.2 r ▸ Set.mem_image_of_mem _ hA
      exact h
    · have e₀ : axisReflectionGroup.toLatticeSymmetry a γ =
          ReflectionPositivity.LatticeAtSpacing.axisReflectionSymmetry a γ := symmetry_ext rfl
      rw [hM.2.2.1 _ A hAobs, e₀]
      rw [symmetry_ext (r' := axisReflectionGroup.toUnitLatticeSymmetry γ)
        (hM.2.2.2.2.2.2.1 γ)]
end YangMills.Construction.ReflectionPositivity.DirectionPictures
