import YangMills.Construction.ReflectionPositivity.OneLatticeAtEverySpacing
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.HalfAndShift
open YangMills.Construction.InfiniteLattice (AmbientSpace LatticePoint GaugeField IsBoundedObservable
  IsLocalObservable IsRegionMeasurable IsSymmetricUnder IsShiftInvariant LatticeMirror
  regionObservables latticeSubgroup shift)
open YangMills.Construction.GibbsAtFixedSpacing (BorelProb)
open YangMills.Construction.ReflectionPositivity.MirrorHyperplanes (MirrorPair IsReflectionPositiveAcross)
open YangMills.Construction.ReflectionPositivity.LatticeAtSpacing (reflectionPositiveSet)
variable {a : ℝ}
theorem smul_normal_mem (P : MirrorPair a) : a • P.normal ∈ latticeSubgroup a := by
  have h : ∀ ι, ∃ m : ℤ, P.normal ι = (m : ℝ) := fun ι => by
    rcases P.normal_apply_trichotomy ι with h | h | h
    · exact ⟨0, by simp [h]⟩
    · exact ⟨1, by simp [h]⟩
    · exact ⟨-1, by simp [h]⟩
  choose m hm using h
  exact ⟨m, fun μ => by simp [hm, mul_comm]⟩
def normalShift (P : MirrorPair a) : LatticePoint a := ⟨a • P.normal, smul_normal_mem P⟩
theorem coe_zsmul_normalShift (P : MirrorPair a) (k : ℤ) :
    ((k • normalShift P : LatticePoint a) : AmbientSpace) = ((k : ℝ) * a) • P.normal := by
  change k • (a • P.normal) = _
  rw [← Int.cast_smul_eq_zsmul ℝ, smul_smul]
def IsReflPosOn (μ : BorelProb a) (P : MirrorPair a) (S : Set AmbientSpace) : Prop :=
  ∀ F : GaugeField a → ℂ, IsLocalObservable F → F ∈ regionObservables a S →
    0 ≤ μ.integral fun U => conj (P.reflect.actOn F U) * F U
def IsReflectionPositiveWithHalf (μ : Measure (GaugeField a)) (Q : LatticeMirror a)
    (H : Set AmbientSpace) : Prop :=
  IsProbabilityMeasure μ ∧ ∀ A : GaugeField a → ℂ,
    IsBoundedObservable A → IsLocalObservable A → IsRegionMeasurable H A →
      0 ≤ ∫ U, A U * Q.conjReflect A U ∂μ
def ReflectionProperties (P : MirrorPair a) : Prop :=
  (∀ x y : AmbientSpace, TorusMetric.euclidNormVec (P.reflect.toFun x - P.reflect.toFun y) =
    TorusMetric.euclidNormVec (x - y)) ∧
  P.reflect.toFun '' (latticeSubgroup a : Set AmbientSpace) = latticeSubgroup a ∧
  P.reflect.toFun ∘ P.reflect.toFun = id ∧
  P.reflect.setImage P.upperHalf = P.lowerHalf ∧
  P.reflect.setImage P.lowerHalf = P.upperHalf ∧
  (∀ x ∈ P.hyperplane, P.reflect.toFun x = x) ∧
  a • P.normal ∈ latticeSubgroup a ∧ a • P.normal ≠ 0 ∧
  (∀ k : ℤ, P.reflect.toFun ∘ (shift (k • normalShift P)).toFun =
    (shift ((-k) • normalShift P)).toFun ∘ P.reflect.toFun) ∧
  ∀ (k : ℤ) (F : GaugeField a → ℂ), IsBoundedObservable F →
    P.reflect.actOn ((shift (k • normalShift P)).actOn F) =
      (shift ((-k) • normalShift P)).actOn (P.reflect.actOn F)
def HalfDeterminesOther (P : MirrorPair a) : Prop :=
  ∀ S S' : Set AmbientSpace,
    (S = P.upperHalf ∧ S' = P.lowerHalf) ∨ (S = P.lowerHalf ∧ S' = P.upperHalf) →
    ∀ μ : BorelProb a, IsSymmetricUnder μ.1 (shift (normalShift P)) → IsReflPosOn μ P S →
      IsSymmetricUnder μ.1 P.reflect ∧ IsReflPosOn μ P S' ∧ IsReflectionPositiveAcross μ.1 P
def PositiveClassChar (a : ℝ) : Prop :=
  reflectionPositiveSet a =
    {μ | IsShiftInvariant μ.1 ∧ ∀ P : MirrorPair a, IsReflectionPositiveAcross μ.1 P} ∧
  (∀ μ ∈ reflectionPositiveSet a, ∀ P : MirrorPair a, IsSymmetricUnder μ.1 P.reflect) ∧
  (fun μ : BorelProb a => μ.1) '' reflectionPositiveSet a = MirrorHyperplanes.positiveClass a ∧
  ∀ (P : MirrorPair a) (Q : LatticeMirror a), Q.plane = P.hyperplane →
    ∀ μ : BorelProb a, IsShiftInvariant μ.1 →
      (∀ H, Q.IsHalfSpace H → (IsReflectionPositiveWithHalf μ.1 Q H ↔
        IsReflectionPositiveAcross μ.1 P)) ∧
      (InfiniteLattice.IsReflectionPositiveAt μ.1 Q ↔ IsReflectionPositiveAcross μ.1 P)
def PositiveClassCharUnit : Prop :=
  (fun μ : BorelProb 1 => μ.1) '' reflectionPositiveSet 1 = MirrorHyperplanes.unitPositiveClass
def HalfAndShiftStatement : Prop :=
  (∀ a : ℝ, 0 < a →
    (∀ P : MirrorPair a, ReflectionProperties P ∧ HalfDeterminesOther P) ∧ PositiveClassChar a) ∧
  PositiveClassCharUnit
end YangMills.Construction.ReflectionPositivity.HalfAndShift
