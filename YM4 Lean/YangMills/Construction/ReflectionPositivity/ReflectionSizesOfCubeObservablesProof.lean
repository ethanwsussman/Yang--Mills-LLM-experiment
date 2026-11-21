import YangMills.Construction.ReflectionPositivity.ActionOfTheLatticeIsometriesTheTwoFieldsAndTheReflections
import YangMills.Construction.ReflectionPositivity.ReflectionSizesOfCubeObservables
import YangMills.Construction.ReflectionPositivity.SignChangesAndTheCube
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open InfiniteLattice (GaugeField halfSpaceLocalObservables observableSupNorm shift
  unitRegionObservables)
open MirrorHyperplanes (unitPositiveClass)
private def reflectedCubeVector (ν : unitPositiveClass) (r : ℕ+)
    (p : Fin 4 × axisReflectionGroup) (A : GaugeField (1 : ℝ) → ℂ) :
    ReflectionPair.site.Hilb ν p.1 :=
  cubeVector ν p.1 r ((axisReflectionGroup.toUnitLatticeSymmetry p.2).actOn A)
private theorem norm_reflectedCubeVector_le_sqrt (ν : unitPositiveClass) (r : ℕ+)
    (p : Fin 4 × axisReflectionGroup) (A : GaugeField (1 : ℝ) → ℂ) :
    ‖reflectedCubeVector ν r p A‖ ≤ cubeReflectionNorm ν r A ^ (1 / 2 : ℝ) := by
  have hsq : ‖reflectedCubeVector ν r p A‖ ^ 2 ≤ cubeReflectionNorm ν r A :=
    (isGreatest_cubeReflectionNorm ν r A).2 ⟨p, rfl⟩
  rw [← Real.sqrt_eq_rpow]
  exact Real.le_sqrt_of_sq_le hsq
private theorem exists_sqrt_cubeReflectionNorm_eq (ν : unitPositiveClass) (r : ℕ+)
    (A : GaugeField (1 : ℝ) → ℂ) :
    ∃ p, cubeReflectionNorm ν r A ^ (1 / 2 : ℝ) = ‖reflectedCubeVector ν r p A‖ := by
  obtain ⟨p, hp⟩ := (isGreatest_cubeReflectionNorm ν r A).1
  refine ⟨p, ?_⟩
  have hp' : ‖reflectedCubeVector ν r p A‖ ^ 2 = cubeReflectionNorm ν r A := hp
  rw [← Real.sqrt_eq_rpow, ← hp']
  exact Real.sqrt_sq (norm_nonneg _)
private theorem obsClass_add (ν : unitPositiveClass) (μ : Fin 4)
    {F G : GaugeField (1 : ℝ) → ℂ} (hF : F ∈ halfSpaceLocalObservables μ)
    (hG : G ∈ halfSpaceLocalObservables μ) :
    ReflectionPair.site.obsClass ν μ (F + G) =
      ReflectionPair.site.obsClass ν μ F + ReflectionPair.site.obsClass ν μ G := by
  simp only [ReflectionPair.obsClass, dif_pos hF, dif_pos hG,
    dif_pos (Submodule.add_mem _ hF hG)]
  exact map_add (FormHilbert.formClass (ReflectionPair.site.pairForm ν μ)) ⟨F, hF⟩ ⟨G, hG⟩
private theorem obsClass_smul (ν : unitPositiveClass) (μ : Fin 4) (a : ℂ)
    {F : GaugeField (1 : ℝ) → ℂ} (hF : F ∈ halfSpaceLocalObservables μ) :
    ReflectionPair.site.obsClass ν μ (a • F) = a • ReflectionPair.site.obsClass ν μ F := by
  simp only [ReflectionPair.obsClass, dif_pos hF, dif_pos (Submodule.smul_mem _ a hF)]
  exact map_smul (FormHilbert.formClass (ReflectionPair.site.pairForm ν μ)) a ⟨F, hF⟩
private theorem shift_reflected_mem_halfSpace (hCube : SignFlipsPreserveCube)
    (ν : unitPositiveClass) (r : ℕ+) (p : Fin 4 × axisReflectionGroup)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r)) :
    (shift ((r : ℕ) • InfiniteLattice.axisStep (1 : ℝ) p.1)).actOn
        ((axisReflectionGroup.toUnitLatticeSymmetry p.2).actOn A) ∈
      halfSpaceLocalObservables p.1 :=
  ((hCube ν p.1 r).2.2.2.2.2 _ ((hCube ν p.1 r).2.2.2.2.1 p.2 A hA)).2.1
private theorem reflectedCubeVector_add (hCube : SignFlipsPreserveCube)
    (ν : unitPositiveClass) (r : ℕ+) (p : Fin 4 × axisReflectionGroup)
    {A B : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r))
    (hB : B ∈ unitRegionObservables (cubeOfRadius r)) :
    reflectedCubeVector ν r p (A + B) = reflectedCubeVector ν r p A + reflectedCubeVector ν r p B :=
  obsClass_add ν p.1 (shift_reflected_mem_halfSpace hCube ν r p hA)
    (shift_reflected_mem_halfSpace hCube ν r p hB)
private theorem reflectedCubeVector_smul (hCube : SignFlipsPreserveCube)
    (ν : unitPositiveClass) (r : ℕ+) (p : Fin 4 × axisReflectionGroup) (a : ℂ)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r)) :
    reflectedCubeVector ν r p (a • A) = a • reflectedCubeVector ν r p A :=
  obsClass_smul ν p.1 a (shift_reflected_mem_halfSpace hCube ν r p hA)
private theorem actOn_actOn_eq_mul
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (g' g : axisReflectionGroup) {A : GaugeField (1 : ℝ) → ℂ}
    (hA : InfiniteLattice.IsBoundedObservable A) :
    (axisReflectionGroup.toUnitLatticeSymmetry g').actOn
        ((axisReflectionGroup.toUnitLatticeSymmetry g).actOn A) =
      (axisReflectionGroup.toUnitLatticeSymmetry (g' * g)).actOn A :=
  ((hAct.2.2.2.2.2.1 (axisReflectionGroup.toUnitLatticeSymmetry g')
    (axisReflectionGroup.toUnitLatticeSymmetry g) A A hA hA).1).symm
private theorem cubeReflectionNorm_actOn
    (hCube : SignFlipsPreserveCube)
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections)
    (ν : unitPositiveClass) (r : ℕ+) (g : axisReflectionGroup)
    {A : GaugeField (1 : ℝ) → ℂ} (hA : A ∈ unitRegionObservables (cubeOfRadius r)) :
    cubeReflectionNorm ν r ((axisReflectionGroup.toUnitLatticeSymmetry g).actOn A) =
      cubeReflectionNorm ν r A := by
  have hset : cubeVectorSqNorms ν r
      ((axisReflectionGroup.toUnitLatticeSymmetry g).actOn A) =
      cubeVectorSqNorms ν r A := by
    ext x
    constructor
    · rintro ⟨⟨μ, g'⟩, rfl⟩
      refine ⟨(μ, g' * g), ?_⟩
      simp only [actOn_actOn_eq_mul hAct g' g hA.1]
    · rintro ⟨⟨μ, g'⟩, rfl⟩
      refine ⟨(μ, g' * g⁻¹), ?_⟩
      simp only [actOn_actOn_eq_mul hAct (g' * g⁻¹) g hA.1, inv_mul_cancel_right]
  rw [cubeReflectionNorm, hset, ← cubeReflectionNorm]
theorem cubeReflectionNormProps_holds (hCube : SignFlipsPreserveCube)
    (hAct : MirrorHyperplanes.SymmetryActionAndReflections) :
    CubeReflectionNormProps := by
  intro ν r
  refine ⟨fun A hA B hB => ?_, fun a A hA => ?_,
    fun g A hA => cubeReflectionNorm_actOn hCube hAct ν r g hA, fun A hA => ?_⟩
  · obtain ⟨p, hp⟩ := exists_sqrt_cubeReflectionNorm_eq ν r (A + B)
    rw [hp, reflectedCubeVector_add hCube ν r p hA hB]
    exact (norm_add_le _ _).trans
      (add_le_add (norm_reflectedCubeVector_le_sqrt ν r p A) (norm_reflectedCubeVector_le_sqrt ν r p B))
  · apply le_antisymm
    · obtain ⟨p, hp⟩ := exists_sqrt_cubeReflectionNorm_eq ν r (a • A)
      rw [hp, reflectedCubeVector_smul hCube ν r p a hA, norm_smul]
      exact mul_le_mul_of_nonneg_left (norm_reflectedCubeVector_le_sqrt ν r p A) (norm_nonneg a)
    · obtain ⟨p, hp⟩ := exists_sqrt_cubeReflectionNorm_eq ν r A
      rw [hp, ← norm_smul, ← reflectedCubeVector_smul hCube ν r p a hA]
      exact norm_reflectedCubeVector_le_sqrt ν r p (a • A)
  · obtain ⟨p, hp⟩ := (isGreatest_cubeReflectionNorm ν r A).1
    have hp' : ‖reflectedCubeVector ν r p A‖ ^ 2 = cubeReflectionNorm ν r A := hp
    rw [← hp']
    have h₁ : ‖reflectedCubeVector ν r p A‖ ≤ observableSupNorm
        ((axisReflectionGroup.toUnitLatticeSymmetry p.2).actOn A) :=
      ((hCube ν p.1 r).2.2.2.2.2 _ ((hCube ν p.1 r).2.2.2.2.1 p.2 A hA)).2.2
    have h₂ : observableSupNorm
        ((axisReflectionGroup.toUnitLatticeSymmetry p.2).actOn A) = observableSupNorm A :=
      ((hAct.2.2.2.2.1 (axisReflectionGroup.toUnitLatticeSymmetry p.2)) A hA.1).2.1
    rw [h₂] at h₁
    exact pow_le_pow_left₀ (norm_nonneg _) h₁ 2
end YangMills.Construction.ReflectionPositivity.DirectionPictures
