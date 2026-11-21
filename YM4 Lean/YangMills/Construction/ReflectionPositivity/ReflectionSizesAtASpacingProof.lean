import YangMills.Construction.ReflectionPositivity.ClassesAndMatrixElementsAtASpacingProof
import YangMills.Construction.ReflectionPositivity.ReflectionSizesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint GaugeField LatticeSymmetry
  IsLocalObservable IsBoundedObservable IsShiftInvariant regionObservables observableSupNorm
  scaledCube pointToUnit pointToUnit_axisStep axisStep shift pullToUnit pushToUnit
  unitRegionObservables)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (unitPositiveClass)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing.UnitScaling (TransportsObservables
  TransportsMeasuresAndSymmetries)
open CoarseStepsInverseSquare
namespace SizesAtMesh
variable {a : ℝ}
theorem latticeSymmetry_ext {b : ℝ} {g g' : LatticeSymmetry b} (h : g.toFun = g'.toFun) :
    g = g' := by apply _root_.YangMills.Construction.ReflectionPositivity.MirrorHyperplanes.latticeSymmetry_ext <;> assumption
theorem isBoundedObservable_conj_mul {b : ℝ} {A B : GaugeField b → ℂ}
    (hA : IsBoundedObservable A) (hB : IsBoundedObservable B) :
    IsBoundedObservable fun U => conj (A U) * B U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.isBoundedObservable_conj_mul <;> assumption
theorem pushToUnit_mem_unitPositiveClass
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) : pushToUnit ν.1 ∈ unitPositiveClass := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.pushToUnit_mem_unitPositiveClass <;> assumption
theorem pullToUnit_shift (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (v : LatticePoint a) {F : GaugeField a → ℂ} (hF : IsBoundedObservable F) :
    pullToUnit ha ((shift v).actOn F) = (shift (pointToUnit ha v)).actOn (pullToUnit ha F) := by
  rw [hM.2.2.1 (shift v) F hF, latticeSymmetry_ext (hM.2.2.2.1 v)]
theorem integral_reflect_pullToUnit (ha : 0 < a) (hM : TransportsMeasuresAndSymmetries ha)
    (ν : BorelProb a)
    (hν : (unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ))) = pushToUnit ν.1)
    (μ : Fin 4) {F H : GaugeField a → ℂ} (hF : IsBoundedObservable F)
    (hH : IsBoundedObservable H) :
    ∫ U, conj ((MirrorHyperplanes.siteReflect μ).actOn (pullToUnit ha F) U) *
        pullToUnit ha H U ∂(unitRepresentative ν.1 : Measure (GaugeField (1 : ℝ))) =
      ν.integral fun U =>
        conj ((LatticeAtSpacing.coordinateReflect a μ).actOn F U) * H U := by apply _root_.YangMills.Construction.ReflectionPositivity.DirectionPictures.ScaledClassesProof.integral_reflect_unitRepresentative <;> assumption
theorem image_centeredCube_subset (ha : 0 < a) (r : ℕ+) {g : Equiv.Perm AmbientSpace}
    (hg : g ∈ axisReflectionGroup) : g '' scaledCube a r ⊆ scaledCube a r := by
  obtain ⟨ε, hε⟩ := exists_signs_of_mem_axisReflectionGroup hg
  rintro _ ⟨y, hy, rfl⟩
  rw [InfiniteLattice.mem_centeredCube ha] at hy ⊢
  intro i
  rw [hε]
  obtain ⟨h₁, h₂⟩ := hy i
  rcases Int.units_eq_one_or (ε i) with e | e
  · rw [e]
    push_cast
    constructor <;> linarith
  · rw [e]
    push_cast
    constructor <;> linarith
theorem imageSet_centeredCube (ha : 0 < a) (r : ℕ+) (γ : axisReflectionGroup) :
    (axisReflectionGroup.toLatticeSymmetry a γ).setImage (scaledCube a r) = scaledCube a r := by
  refine Subset.antisymm (image_centeredCube_subset ha r γ.2) fun x hx => ?_
  refine ⟨γ.1⁻¹ x, image_centeredCube_subset ha r (inv_mem γ.2) ⟨x, hx, rfl⟩, ?_⟩
  change γ.1 (γ.1⁻¹ x) = x
  simp
theorem axisReflectObs_image (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a)
    (r : ℕ+) (γ : axisReflectionGroup) :
    axisReflectObs γ '' regionObservables a (scaledCube a r) = regionObservables a (scaledCube a r) := by
  have h := ((hFrame a ha).2.2.1 (axisReflectionGroup.toLatticeSymmetry a γ)
    (axisReflectionGroup.toLatticeSymmetry a γ)).2.2.2.2.2.2.2.2.1 (scaledCube a r)
  rw [imageSet_centeredCube ha r γ] at h
  exact h
theorem axisReflectObs_mem (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a)
    (r : ℕ+) (γ : axisReflectionGroup) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    axisReflectObs γ A ∈ regionObservables a (scaledCube a r) :=
  axisReflectObs_image hFrame ha r γ ▸ mem_image_of_mem _ hA
theorem cubeVector_transport (hCl : ScaledClassesTheorem) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (μ : Fin 4) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) (γ : axisReflectionGroup) :
    ScaledPair.cubeVector ν.1 μ ha r A =
        cubeVector (unitRepresentative ν.1) μ r (pullToUnit ha A) ∧
      pullToUnit ha A ∈ unitRegionObservables (cubeOfRadius r) ∧
      pullToUnit ha (axisReflectObs γ A) =
        (axisReflectionGroup.toUnitLatticeSymmetry γ).actOn (pullToUnit ha A) := by
  obtain ⟨-, -, h₂, h₃, h₄, h₅, h₆, -⟩ := (hCl a ha ν hν μ).2.2 0 (zero_mem _) r A hA γ
  exact ⟨h₂.trans (h₃.trans h₄), h₅, h₆⟩
theorem cubeVecNorm_sq_eq (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (μ : Fin 4) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    ((cubeVecNorm ha ν μ r A ^ 2 : ℝ) : ℂ) = cubeReflectedCorrelation ν μ r A := by
  obtain ⟨-, hM, -, -, -⟩ := hDict a ha
  have hcoe := coe_unitRepresentative (pushToUnit_mem_unitPositiveClass hDict hHalf ha hν)
  obtain ⟨hv, hunit, -⟩ := cubeVector_transport hCl ha hν μ r hA 1
  have h := (hSite (unitRepresentative ν.1) μ r).2.2.2.2.1.2.2 _ hunit
  have hobs : IsBoundedObservable A := hA.1
  have hsh := pullToUnit_shift ha hM ((2 * (r : ℕ)) • axisStep a μ) hobs
  rw [map_nsmul, pointToUnit_axisStep] at hsh
  rw [cubeVecNorm, hv, h, ← hsh]
  exact integral_reflect_pullToUnit ha hM ν hcoe μ hobs (hobs.actOn _)
theorem isGreatest_reflectedCorrelations (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    IsGreatest
      (Set.range fun p : Fin 4 × axisReflectionGroup =>
        (cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 A)).re)
      (reflectionSize ha ν r A) := by
  have e : (Set.range fun p : Fin 4 × axisReflectionGroup =>
      (cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 A)).re) =
      scaledCubeVectorNormsSq ha ν.1 r A := by
    rw [scaledCubeVectorNormsSq]
    congr 1
    funext p
    rw [← cubeVecNorm_sq_eq hSite hCl hDict hHalf ha hν p.1 r
      (axisReflectObs_mem hFrame ha r p.2 hA), Complex.ofReal_re]
    rfl
  rw [e]
  exact isGreatest_scaledCubeReflectionSize ha ν.1 r A
theorem reflectionSize_eq_unit (hCl : ScaledClassesTheorem)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    reflectionSize ha ν r A =
      cubeReflectionNorm (unitRepresentative ν.1) r (pullToUnit ha A) := by
  rw [reflectionSize, scaledCubeReflectionSize, cubeReflectionNorm, scaledCubeVectorNormsSq,
    cubeVectorSqNorms]
  congr 2
  funext p
  obtain ⟨h₁, -, -⟩ := cubeVector_transport hCl ha hν p.1 r (axisReflectObs_mem hFrame ha r p.2 hA) 1
  obtain ⟨-, -, h₃⟩ := cubeVector_transport hCl ha hν p.1 r hA p.2
  change ‖ScaledPair.cubeVector ν.1 p.1 ha r (axisReflectObs p.2 A)‖ ^ 2 = _
  rw [h₁, h₃]
theorem borelProb_integral_eq (ν : BorelProb a) (F : GaugeField a → ℂ) :
    ν.integral F = ∫ U, F U ∂ν.1 :=
  rfl
theorem cubeReflectedCorrelation_conj (ν : BorelProb a) (μ : Fin 4) (r : ℕ+)
    (B : GaugeField a → ℂ) :
    cubeReflectedCorrelation ν μ r (fun U => conj (B U)) =
      conj (cubeReflectedCorrelation ν μ r B) := by
  rw [cubeReflectedCorrelation, cubeReflectedCorrelation,
    CoarseStepsInverseSquare.reflectedCorrelation, CoarseStepsInverseSquare.reflectedCorrelation,
    borelProb_integral_eq, borelProb_integral_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
  simp only [reflectShiftProduct, map_mul]
  rfl
theorem conj_mem_regionObservables (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    (fun U => conj (A U)) ∈ regionObservables a (scaledCube a r) := by
  obtain ⟨⟨mA, C, hC⟩, hm⟩ := hA
  refine ⟨⟨Complex.continuous_conj.measurable.comp mA, C, fun U => ?_⟩,
    Complex.continuous_conj.measurable.comp hm⟩
  rw [RCLike.norm_conj]
  exact hC U
theorem reflectionSize_conj (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    reflectionSize ha ν r A = reflectionSize ha ν r (fun U => conj (A U)) := by
  rw [reflectionSize, reflectionSize, scaledCubeReflectionSize, scaledCubeReflectionSize,
    scaledCubeVectorNormsSq, scaledCubeVectorNormsSq]
  congr 2
  funext p
  have h₁ := cubeVecNorm_sq_eq hSite hCl hDict hHalf ha hν p.1 r
    (axisReflectObs_mem hFrame ha r p.2 hA)
  have h₂ := cubeVecNorm_sq_eq hSite hCl hDict hHalf ha hν p.1 r
    (axisReflectObs_mem hFrame ha r p.2 (conj_mem_regionObservables r hA))
  have e : axisReflectObs p.2 (fun U => conj (A U)) = fun U => conj (axisReflectObs p.2 A U) :=
    rfl
  rw [e, cubeReflectedCorrelation_conj, ← h₁, Complex.conj_ofReal] at h₂
  exact (Complex.ofReal_injective h₂).symm
theorem reflectionSize_one (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a) {ν : BorelProb a}
    (hν : ν ∈ reflectionPositiveSet a) (r : ℕ+) :
    reflectionSize ha ν r (fun _ => 1) = 1 := by
  have h1 : (fun _ : GaugeField a => (1 : ℂ)) ∈ regionObservables a (scaledCube a r) :=
    ⟨⟨measurable_const, 1, fun _ => by simp⟩, measurable_const⟩
  obtain ⟨⟨p, hp⟩, -⟩ := isGreatest_reflectedCorrelations hSite hCl hDict hHalf hFrame ha hν r h1
  rw [← hp]
  have := ν.2
  have e : cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 fun _ => 1) = 1 := by
    change ∫ _, conj (1 : ℂ) * 1 ∂ν.1 = 1
    simp
  change (cubeReflectedCorrelation ν p.1 r (axisReflectObs p.2 fun _ => 1)).re = 1
  rw [e]
  rfl
theorem integral_convexMix (t : unitInterval) (ν₁ ν₂ : BorelProb a) {G : GaugeField a → ℂ}
    (hG : IsBoundedObservable G) :
    (convexMix t ν₁ ν₂).integral G =
      ((t : ℝ) : ℂ) * ν₁.integral G + ((1 - (t : ℝ) : ℝ) : ℂ) * ν₂.integral G := by
  have := ν₁.2
  have := ν₂.2
  obtain ⟨mG, C, hC⟩ := hG
  have i₁ : Integrable G ν₁.1 :=
    Integrable.of_bound mG.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  have i₂ : Integrable G ν₂.1 :=
    Integrable.of_bound mG.aestronglyMeasurable C (Filter.Eventually.of_forall hC)
  change ∫ U, G U ∂(ENNReal.ofReal (t : ℝ) • ν₁.1 + ENNReal.ofReal (1 - (t : ℝ)) • ν₂.1) = _
  rw [integral_add_measure (i₁.smul_measure ENNReal.ofReal_ne_top)
      (i₂.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal t.2.1, ENNReal.toReal_ofReal (sub_nonneg.mpr t.2.2), Complex.real_smul,
    Complex.real_smul]
  rfl
theorem convexMix_mem {ν₁ ν₂ : BorelProb a} (h₁ : ν₁ ∈ reflectionPositiveSet a)
    (h₂ : ν₂ ∈ reflectionPositiveSet a) (t : unitInterval) :
    convexMix t ν₁ ν₂ ∈ reflectionPositiveSet a := by
  refine ⟨fun v A hA => ?_, fun P F hl hF => ?_⟩
  · have e₁ : ν₁.integral ((shift v).actOn A) = ν₁.integral A := h₁.1 v A hA
    have e₂ : ν₂.integral ((shift v).actOn A) = ν₂.integral A := h₂.1 v A hA
    change (convexMix t ν₁ ν₂).integral _ = (convexMix t ν₁ ν₂).integral A
    rw [integral_convexMix t ν₁ ν₂ hA, integral_convexMix t ν₁ ν₂ (hA.actOn _), e₁, e₂]
  · have hO : IsBoundedObservable fun U => conj (P.reflect.actOn F U) * F U :=
      isBoundedObservable_conj_mul (hF.1.actOn _) hF.1
    rw [integral_convexMix t ν₁ ν₂ hO]
    exact add_nonneg (mul_nonneg (Complex.zero_le_real.2 t.2.1) (h₁.2 P F hl hF))
      (mul_nonneg (Complex.zero_le_real.2 (sub_nonneg.2 t.2.2)) (h₂.2 P F hl hF))
theorem isBoundedObservable_reflectShiftProduct (μ : Fin 4) {F : GaugeField a → ℂ}
    (hF : IsBoundedObservable F) (v : LatticePoint a) :
    IsBoundedObservable (reflectShiftProduct μ F v) :=
  isBoundedObservable_conj_mul (hF.actOn _) (hF.actOn _)
theorem reflectionSize_convexMix_le (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hHalf : HalfAndShift.HalfAndShiftStatement)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing) (ha : 0 < a) {ν₁ ν₂ : BorelProb a}
    (h₁ : ν₁ ∈ reflectionPositiveSet a) (h₂ : ν₂ ∈ reflectionPositiveSet a)
    (t : unitInterval) (r : ℕ+) {A : GaugeField a → ℂ}
    (hA : A ∈ regionObservables a (scaledCube a r)) :
    reflectionSize ha (convexMix t ν₁ ν₂) r A ≤
      (t : ℝ) * reflectionSize ha ν₁ r A + (1 - (t : ℝ)) * reflectionSize ha ν₂ r A := by
  obtain ⟨⟨p, hp⟩, -⟩ :=
    isGreatest_reflectedCorrelations hSite hCl hDict hHalf hFrame ha (convexMix_mem h₁ h₂ t) r hA
  have b₁ : (cubeReflectedCorrelation ν₁ p.1 r (axisReflectObs p.2 A)).re ≤
      reflectionSize ha ν₁ r A :=
    (isGreatest_reflectedCorrelations hSite hCl hDict hHalf hFrame ha h₁ r hA).2 ⟨p, rfl⟩
  have b₂ : (cubeReflectedCorrelation ν₂ p.1 r (axisReflectObs p.2 A)).re ≤
      reflectionSize ha ν₂ r A :=
    (isGreatest_reflectedCorrelations hSite hCl hDict hHalf hFrame ha h₂ r hA).2 ⟨p, rfl⟩
  have hO := isBoundedObservable_reflectShiftProduct p.1 (axisReflectObs_mem hFrame ha r p.2 hA).1
    ((2 * (r : ℕ)) • axisStep a p.1)
  rw [← hp]
  change ((convexMix t ν₁ ν₂).integral (reflectShiftProduct p.1 (axisReflectObs p.2 A) _)).re ≤ _
  rw [integral_convexMix t ν₁ ν₂ hO, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul]
  exact add_le_add (mul_le_mul_of_nonneg_left b₁ t.2.1)
    (mul_le_mul_of_nonneg_left b₂ (sub_nonneg.2 t.2.2))
end SizesAtMesh
open SizesAtMesh in
theorem reflectionSizeBoundsAtMesh_holds
    (hSite : SiteReflectionPair.Conclusion)
    (hCl : ScaledClassesTheorem)
    (hDict : LatticeAtSpacing.UnitScaling.UnitScalingDictionary)
    (hFrame : LatticeAtSpacing.LatticeFrameAtSpacing)
    (hHalf : HalfAndShift.HalfAndShiftStatement) :
    ReflectionSizeBoundsAtMesh := by
  intro a ha ν hν r
  obtain ⟨hSp, -, -, -, -⟩ := hDict a ha
  have hCubes := (hSite (unitRepresentative ν.1) 0 r).1
  have hSizes := (hSite (unitRepresentative ν.1) 0 r).2.2.2.2.2
  have hcard : Nat.card axisReflectionGroup = 16 := hCubes.2.1
  refine ⟨⟨fun γ => ⟨imageSet_centeredCube ha r γ, axisReflectObs_image hFrame ha r γ⟩, hCubes.1,
    hcard⟩, fun A hA => ?_, ?_, reflectionSize_one hSite hCl hDict hHalf hFrame ha hν r, ?_⟩
  · have hnorm : ∀ (μ : Fin 4) {B : GaugeField a → ℂ},
        B ∈ regionObservables a (scaledCube a r) →
        ((cubeVecNorm ha ν μ r B ^ 2 : ℝ) : ℂ) = cubeReflectedCorrelation ν μ r B :=
      fun μ _ hB => cubeVecNorm_sq_eq hSite hCl hDict hHalf ha hν μ r hB
    refine ⟨fun μ => hnorm μ hA, isGreatest_scaledCubeReflectionSize ha ν.1 r A,
      fun μ γ => ⟨?_, hnorm μ (axisReflectObs_mem hFrame ha r γ hA)⟩, ?_,
      isGreatest_reflectedCorrelations hSite hCl hDict hHalf hFrame ha hν r hA, fun μ γ => ?_,
      reflectionSize_eq_unit hCl hFrame ha hν r hA⟩
    · obtain ⟨h₁, -, -⟩ := cubeVector_transport hCl ha hν μ r (axisReflectObs_mem hFrame ha r γ hA) 1
      obtain ⟨-, -, h₃⟩ := cubeVector_transport hCl ha hν μ r hA γ
      rw [cubeVecNorm, h₁, h₃]
    · rw [Nat.card_prod, hcard]
      simp
    · rw [← hnorm μ (axisReflectObs_mem hFrame ha r γ hA)]
      exact Complex.zero_le_real.2 (sq_nonneg _)
  · have hunit : ∀ A ∈ regionObservables a (scaledCube a r),
        pullToUnit ha A ∈ cubeObservableSpace r := fun A hA =>
      (cubeVector_transport hCl ha hν 0 r hA 1).2.1
    let L : cubeObsSubmodule a r →ₗ[ℂ] cubeObservableSpace r :=
      { toFun := fun A => ⟨pullToUnit ha A, hunit A A.2⟩
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    obtain ⟨p, hp⟩ := hSizes.1
    refine ⟨⟨p.comp L, fun A => ?_⟩, fun A hA => ⟨fun γ => ?_,
      reflectionSize_conj hSite hCl hDict hHalf hFrame ha hν r hA, ?_⟩⟩
    · rw [Seminorm.comp_apply, hp, reflectionSize_eq_unit hCl hFrame ha hν r A.2]
      rfl
    · obtain ⟨-, hm, h₃⟩ := cubeVector_transport hCl ha hν 0 r hA γ
      rw [reflectionSize_eq_unit hCl hFrame ha hν r (axisReflectObs_mem hFrame ha r γ hA), h₃,
        hSizes.2.1 γ _ hm, reflectionSize_eq_unit hCl hFrame ha hν r hA]
    · have hm := (cubeVector_transport hCl ha hν 0 r hA 1).2.1
      have hn := (hSp.2.2.2.2.2.2.1 A hA.1).2.1
      rw [reflectionSize_eq_unit hCl hFrame ha hν r hA, ← hn]
      exact hSizes.2.2 _ hm
  · refine ⟨fun A hA μ γ => ⟨isBoundedObservable_reflectShiftProduct μ
        (axisReflectObs_mem hFrame ha r γ hA).1 _,
      fun ν₁ ν₂ t => integral_convexMix t ν₁ ν₂
        (isBoundedObservable_reflectShiftProduct μ (axisReflectObs_mem hFrame ha r γ hA).1 _)⟩,
      fun ν₁ h₁ ν₂ h₂ t => ⟨convexMix_mem h₁ h₂ t, fun A hA =>
        reflectionSize_convexMix_le hSite hCl hDict hHalf hFrame ha h₁ h₂ t r hA⟩⟩
end YangMills.Construction.ReflectionPositivity.DirectionPictures
