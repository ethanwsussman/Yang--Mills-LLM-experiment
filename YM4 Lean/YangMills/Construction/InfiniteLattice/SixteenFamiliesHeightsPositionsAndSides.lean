import YangMills.Construction.InfiniteLattice.ObservablesHypercubicLatticeMapsAndHyperplanes
import YangMills.Construction.InfiniteLattice.SpecificationGaugeTransformationsAndClassesOfMeasures
import YangMills.Construction.Lattice.LevelCoordinates
import Mathlib
set_option autoImplicit false
open Set
open scoped ComplexConjugate Matrix
noncomputable section
namespace YangMills.Construction
namespace NormalFamilies
open InfiniteLattice
open PeriodicLattice (coordVec)
def normalSet : Set AmbientSpace :=
  {n | (∃ μ : Fin 4, n = coordVec μ) ∨
    ∃ μ lam : Fin 4, μ < lam ∧
      (n = coordVec μ + coordVec lam ∨
        n = coordVec μ - coordVec lam)}
def normSq (n : AmbientSpace) : ℝ := TorusMetric.euclidNormVec n ^ 2
theorem normSq_eq_dotProduct (n : AmbientSpace) : normSq n = n ⬝ᵥ n := by
  rw [normSq, TorusMetric.euclidNormVec,
    Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  exact Finset.sum_congr rfl fun μ _ => sq (n μ)
def dualVector (n : AmbientSpace) : AmbientSpace := (normSq n)⁻¹ • n
def firstNonzeroIndex (n : AmbientSpace) : Fin 4 := sInf {μ | n μ ≠ 0}
theorem firstNonzeroIndex_spec {n : AmbientSpace} (hn : ∃ μ, n μ ≠ 0) :
    n (firstNonzeroIndex n) ≠ 0 ∧ ∀ κ, κ < firstNonzeroIndex n → n κ = 0 := by
  have hne : {μ : Fin 4 | n μ ≠ 0}.Nonempty := hn
  refine ⟨hne.csInf_mem (Set.toFinite _), fun κ hκ => ?_⟩
  by_contra h
  exact absurd (csInf_le' (show κ ∈ {μ | n μ ≠ 0} from h)) (not_le.mpr hκ)
def firstNonzeroBasisVec (n : AmbientSpace) : AmbientSpace := coordVec (firstNonzeroIndex n)
def linearHeight (n x : AmbientSpace) : ℝ := n ⬝ᵥ x
def IsDiagonalNormal (n : AmbientSpace) : Prop := normSq n = 2
def reflectAcross (n : AmbientSpace) (c : ℝ) (x : AmbientSpace) : AmbientSpace :=
  x - (2 * (n ⬝ᵥ x - c)) • dualVector n
theorem reflectAcross_eq_hyperplaneReflect (n : AmbientSpace) (c : ℝ) :
    reflectAcross n c = hyperplaneReflect n c := by
  funext x
  simp only [reflectAcross, hyperplaneReflect, dualVector, normSq_eq_dotProduct, smul_smul]
  rfl
def IsAllowedLevel (a : ℝ) (n : AmbientSpace) (c : ℝ) : Prop :=
  (normSq n = 1 → ∃ k : ℤ, c = (k : ℝ) * (a / 2)) ∧
    (normSq n = 2 → ∃ k : ℤ, c = (k : ℝ) * a)
theorem isAllowedLevel_one_iff (n : AmbientSpace) (c : ℝ) :
    IsAllowedLevel 1 n c ↔
      (normSq n = 1 → ∃ k : ℤ, c = (k : ℝ) / 2) ∧
        (normSq n = 2 → ∃ k : ℤ, c = (k : ℝ)) := by
  simp only [IsAllowedLevel, mul_one, mul_one_div]
structure NormalLevelPair (a : ℝ) where
  normal : AmbientSpace
  normal_mem : normal ∈ normalSet
  level : ℝ
  allowed : IsAllowedLevel a normal level
theorem exists_reflectionClass {n : AmbientSpace} (h : n ∈ normalSet) :
    ∃ F : ReflectionClass, F.realNormal = n := by
  rcases h with ⟨μ, rfl⟩ | ⟨μ, lam, hlt, rfl | rfl⟩
  · refine ⟨.axial μ, funext fun κ => ?_⟩
    by_cases h : κ = μ
    · subst h
      simp [ReflectionClass.realNormal, ReflectionClass.intNormal, coordVec]
    · simp [ReflectionClass.realNormal, ReflectionClass.intNormal, coordVec,
        Pi.single_eq_of_ne h]
  · refine ⟨.diagonal μ lam hlt 1, funext fun κ => ?_⟩
    simp only [ReflectionClass.realNormal, ReflectionClass.intNormal, coordVec, Pi.add_apply,
      Units.val_one, one_smul, Int.cast_add]
    congr 1 <;> simp [Pi.single_apply]
  · refine ⟨.diagonal μ lam hlt (-1), funext fun κ => ?_⟩
    simp only [ReflectionClass.realNormal, ReflectionClass.intNormal, coordVec, Pi.add_apply,
      Pi.sub_apply, Units.val_neg, Units.val_one, neg_smul, one_smul, Pi.neg_apply, Int.cast_add,
      Int.cast_neg, sub_eq_add_neg]
    congr 1 <;> simp [Pi.single_apply]
namespace NormalLevelPair
variable {a : ℝ} (P : NormalLevelPair a)
def IsSitePair : Prop := normSq P.normal = 1 ∧ ∃ k : ℤ, P.level = (k : ℝ) * a
def IsLinkPair : Prop := normSq P.normal = 1 ∧ ∃ k : ℤ, P.level = (k : ℝ) * a + a / 2
def IsDiagonalPair : Prop := normSq P.normal = 2
def toLatticeMirror : LatticeMirror a where
  cls := (exists_reflectionClass P.normal_mem).choose
  level := P.level
  level_mem := by
    have hF := (exists_reflectionClass P.normal_mem).choose_spec
    generalize (exists_reflectionClass P.normal_mem).choose = F at hF
    cases F with
    | axial μ =>
      obtain ⟨k, hk⟩ := P.allowed.1 (by
        rw [normSq_eq_dotProduct, ← hF, ReflectionClass.realNormal_dot_axial])
      exact ⟨k, hk⟩
    | diagonal μ lam hlt s =>
      obtain ⟨k, hk⟩ := P.allowed.2 (by
        rw [normSq_eq_dotProduct, ← hF, ReflectionClass.realNormal_dot_diagonal])
      exact ⟨k, hk⟩
theorem toLatticeMirror_realNormal : P.toLatticeMirror.cls.realNormal = P.normal :=
  (exists_reflectionClass P.normal_mem).choose_spec
def reflectSymmetry : LatticeSymmetry a where
  toFun := reflectAcross P.normal P.level
  preservesDist := by
    rw [reflectAcross_eq_hyperplaneReflect, ← P.toLatticeMirror_realNormal]
    exact euclidNormVec_hyperplaneReflect_sub P.toLatticeMirror.cls.realNormal_dot_ne_zero P.level
  image_eq := by
    have h := P.toLatticeMirror.symmetry.image_eq
    have hf : P.toLatticeMirror.symmetry.toFun = reflectAcross P.normal P.level := by
      rw [reflectAcross_eq_hyperplaneReflect, ← P.toLatticeMirror_realNormal]
      rfl
    rwa [hf] at h
def reflectObservable (F : GaugeField a → ℂ) : GaugeField a → ℂ :=
  P.reflectSymmetry.actOn F
def conjReflectObservable (F : GaugeField a → ℂ) : GaugeField a → ℂ :=
  fun U => conj (P.reflectObservable F U)
end NormalLevelPair
def closedHalfSpace (n : AmbientSpace) (c : ℝ) (ε : ℤˣ) : Set AmbientSpace :=
  {x | 0 ≤ ((ε : ℤ) : ℝ) * (n ⬝ᵥ x - c)}
def halfSpaceLinks (a : ℝ) (n : AmbientSpace) (c : ℝ) (ε : ℤˣ) : Set (Link a) :=
  {b | b ∈ positiveLinks a ∧ LinksLieIn {b} (closedHalfSpace n c ε)}
def planeLinks (a : ℝ) (n : AmbientSpace) (c : ℝ) : Set (Link a) :=
  halfSpaceLinks a n c 1 ∩ halfSpaceLinks a n c (-1)
def crossingLinks (a : ℝ) (n : AmbientSpace) (c : ℝ) : Set (Link a) :=
  positiveLinks a \ (halfSpaceLinks a n c 1 ∪ halfSpaceLinks a n c (-1))
def halfSpaceObservables (a : ℝ) (n : AmbientSpace) (c : ℝ) (ε : ℤˣ) :
    Set (GaugeField a → ℂ) :=
  regionObservables a (closedHalfSpace n c ε)
def halfSpaceContinuousLocal (a : ℝ) (n : AmbientSpace) (c : ℝ) (ε : ℤˣ) :
    Set (GaugeField a → ℂ) :=
  halfSpaceObservables a n c ε ∩ continuousLocalFunctions a
def IsCutBy {a : ℝ} (p : ElementaryPlaquette a) (n : AmbientSpace) (c : ℝ) : Prop :=
  ¬ p.linkSet ⊆ halfSpaceLinks a n c 1 ∧ ¬ p.linkSet ⊆ halfSpaceLinks a n c (-1)
end NormalFamilies
end YangMills.Construction
