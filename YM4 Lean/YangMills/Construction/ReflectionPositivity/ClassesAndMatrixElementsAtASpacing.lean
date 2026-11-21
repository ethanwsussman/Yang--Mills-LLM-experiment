import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import YangMills.Construction.ReflectionPositivity.PicturesCubeVectorsAndReflectionSizesAtASpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.DirectionPictures
open YangMills.Construction.InfiniteLattice (GaugeField IsLocalObservable closedHalfSpace
  halfSpaceLocalObservables regionObservables observableSupNorm scaledCube pointOfUnit axisStep shift
  pullToUnit unitRegionObservables)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
variable {a : ℝ}
def halfSpaceLocalAtMesh (a : ℝ) (μ : Fin 4) : Submodule ℂ (GaugeField a → ℂ) where
  carrier := {A | A ∈ regionObservables a (closedHalfSpace μ) ∧ IsLocalObservable A}
  add_mem' := by
    rintro A B ⟨⟨hA, mA⟩, lA⟩ ⟨⟨hB, mB⟩, lB⟩
    exact ⟨⟨hA.add hB, Measurable.add mA mB⟩, lA.add lB⟩
  zero_mem' :=
    ⟨⟨⟨measurable_const, 0, fun _ => by simp⟩, measurable_const⟩,
      ∅, Bornology.isBounded_empty, measurable_const⟩
  smul_mem' := by
    rintro z A ⟨⟨hA, mA⟩, S, bS, mS⟩
    exact ⟨⟨hA.const_smul z, Measurable.const_smul mA z⟩, S, bS, Measurable.const_smul mS z⟩
theorem mem_halfSpaceLocalAtMesh_iff (a : ℝ) (μ : Fin 4) (A : GaugeField a → ℂ) :
    A ∈ halfSpaceLocalAtMesh a μ ↔
      A ∈ regionObservables a (closedHalfSpace μ) ∧ IsLocalObservable A :=
  Iff.rfl
def reflectedFormAtMesh (ν : BorelProb a) (μ : Fin 4) :
    YangMills.Construction.HilbertSpace.SesqForm (halfSpaceLocalAtMesh a μ) :=
  fun F H => ν.integral fun U =>
    conj ((LatticeAtSpacing.coordinateReflect a μ).actOn
      (F : GaugeField a → ℂ) U) * (H : GaugeField a → ℂ) U
def ScaledClassesTheorem : Prop :=
  ∀ (a : ℝ) (ha : 0 < a) (ν : BorelProb a), ν ∈ reflectionPositiveSet a → ∀ μ : Fin 4,
    (pullToUnit ha '' (halfSpaceLocalAtMesh a μ : Set (GaugeField a → ℂ)) =
        (halfSpaceLocalObservables μ : Set (GaugeField (1 : ℝ) → ℂ)) ∧
      (∃ f : halfSpaceLocalAtMesh a μ →ₗ[ℂ] ScaledPair.Hilb ν.1 μ,
        (∀ F, f F = ScaledPair.obsClass ν.1 μ ha (F : GaugeField a → ℂ)) ∧
        Dense (Set.range f)) ∧
      ∀ F ∈ halfSpaceLocalAtMesh a μ,
        ‖ScaledPair.obsClass ν.1 μ ha F‖ ≤ observableSupNorm F) ∧
    ((∀ F ∈ halfSpaceLocalAtMesh a μ, ∀ H ∈ halfSpaceLocalAtMesh a μ,
        ∀ (n : ℕ) (w : Fin 4 → ℤ), w μ = 0 →
        inner ℂ (ScaledPair.obsClass ν.1 μ ha F)
            ((ScaledPair.transferOp ν.1 μ ^ n * ScaledPair.shiftMonomial ν.1 μ w)
              (ScaledPair.obsClass ν.1 μ ha H)) =
          ν.integral fun U => conj ((LatticeAtSpacing.coordinateReflect a μ).actOn F U) *
            (shift (pointOfUnit a (n • axisStep 1 μ + intPoint w))).actOn H U) ∧
      (∀ F ∈ halfSpaceLocalAtMesh a μ,
        ScaledPair.transferOp ν.1 μ (ScaledPair.obsClass ν.1 μ ha F) =
            ScaledPair.obsClass ν.1 μ ha
              ((shift (axisStep a μ)).actOn F) ∧
          ∀ l : TransverseAxis μ,
            ScaledPair.shiftOp ν.1 μ l
                (ScaledPair.obsClass ν.1 μ ha F) =
              ScaledPair.obsClass ν.1 μ ha
                ((shift (axisStep a l.1)).actOn F)) ∧
      (∀ F H : halfSpaceLocalAtMesh a μ,
        inner ℂ (ScaledPair.obsClass ν.1 μ ha (F : GaugeField a → ℂ))
            (ScaledPair.obsClass ν.1 μ ha (H : GaugeField a → ℂ)) =
          reflectedFormAtMesh ν μ F H) ∧
      YangMills.Construction.FormHilbert.IsPosSesqForm (reflectedFormAtMesh ν μ) ∧
      (reflectedFormAtMesh ν μ).IsConjSymm) ∧
    ∀ F ∈ halfSpaceLocalAtMesh a μ, ∀ (r : ℕ+), ∀ A ∈ regionObservables a (scaledCube a r),
      ∀ γ : axisReflectionGroup,
      (shift ((r : ℕ) • axisStep a μ)).actOn A ∈ halfSpaceLocalAtMesh a μ ∧
      ScaledPair.obsClass ν.1 μ ha F =
        ReflectionPair.site.obsClass (unitRepresentative ν.1) μ (pullToUnit ha F) ∧
      ScaledPair.cubeVector ν.1 μ ha r A =
        ScaledPair.obsClass ν.1 μ ha
          ((shift ((r : ℕ) • axisStep a μ)).actOn A) ∧
      ScaledPair.obsClass ν.1 μ ha
          ((shift ((r : ℕ) • axisStep a μ)).actOn A) =
        ReflectionPair.site.obsClass (unitRepresentative ν.1) μ
          ((shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn (pullToUnit ha A)) ∧
      ReflectionPair.site.obsClass (unitRepresentative ν.1) μ
          ((shift ((r : ℕ) • axisStep (1 : ℝ) μ)).actOn (pullToUnit ha A)) =
        cubeVector (unitRepresentative ν.1) μ r (pullToUnit ha A) ∧
      pullToUnit ha A ∈ unitRegionObservables (cubeOfRadius r) ∧
      pullToUnit ha ((axisReflectionGroup.toLatticeSymmetry a γ).actOn A) =
        (axisReflectionGroup.toUnitLatticeSymmetry γ).actOn (pullToUnit ha A) ∧
      pullToUnit ha (fun U => conj (A U)) = fun U => conj (pullToUnit ha A U)
end YangMills.Construction.ReflectionPositivity.DirectionPictures
