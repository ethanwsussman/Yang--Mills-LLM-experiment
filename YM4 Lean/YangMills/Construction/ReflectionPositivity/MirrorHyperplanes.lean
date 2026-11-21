import YangMills.Construction.InfiniteLattice.GaugeFieldsAndStates
import Mathlib
set_option autoImplicit false
open MeasureTheory Set
open scoped ComplexConjugate ComplexOrder Matrix
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
open InfiniteLattice (AmbientSpace GaugeField IsBoundedObservable IsLocalObservable
  IsRegionMeasurable LatticeSymmetry LatticeMirror ReflectionClass hyperplaneReflect)
abbrev basisVec (μ : Fin 4) : AmbientSpace := Pi.single μ 1
def IsIntMultiple (a c : ℝ) : Prop := ∃ q : ℤ, c = (q : ℝ) * a
def IsHalfIntMultiple (a c : ℝ) : Prop := ∃ q : ℤ, c = (q : ℝ) * (a / 2)
def IsDiagonalDirection (n : AmbientSpace) : Prop :=
  ∃ μ κ : Fin 4, μ ≠ κ ∧ (n = basisVec μ + basisVec κ ∨ n = basisVec μ - basisVec κ)
structure MirrorPair (a : ℝ) where
  normal : AmbientSpace
  height : ℝ
  admissible : ((∃ μ, normal = basisVec μ) ∧ IsHalfIntMultiple a height) ∨
    (IsDiagonalDirection normal ∧ IsIntMultiple a height)
abbrev UnitMirrorPair : Type := MirrorPair 1
namespace MirrorPair
variable {a : ℝ} (P : MirrorPair a)
def hyperplane : Set AmbientSpace := {x | P.normal ⬝ᵥ x = P.height}
def halfSpaces : Set (Set AmbientSpace) :=
  {{x | P.height ≤ P.normal ⬝ᵥ x}, {x | P.normal ⬝ᵥ x ≤ P.height}}
end MirrorPair
def IsMirrorPlaneOf (a : ℝ) (S : Set AmbientSpace) : Prop := ∃ P : MirrorPair a, P.hyperplane = S
theorem hyperplaneReflect_neg (n : AmbientSpace) (c : ℝ) :
    hyperplaneReflect (-n) (-c) = hyperplaneReflect n c := by
  funext x κ
  simp only [hyperplaneReflect, neg_dotProduct, dotProduct_neg, neg_neg, Pi.sub_apply,
    Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
  ring
theorem realNormal_axial (μ : Fin 4) : (ReflectionClass.axial μ).realNormal = basisVec μ := by
  funext κ
  by_cases h : κ = μ
  · subst h
    simp [ReflectionClass.realNormal, ReflectionClass.intNormal]
  · simp [ReflectionClass.realNormal, ReflectionClass.intNormal, Pi.single_eq_of_ne h]
theorem realNormal_diagonal_one (μ ν : Fin 4) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt 1).realNormal = basisVec μ + basisVec ν := by
  funext κ
  by_cases h : κ = μ <;> by_cases h' : κ = ν <;>
    simp [ReflectionClass.realNormal, ReflectionClass.intNormal, Pi.single_apply, h, h']
theorem realNormal_diagonal_neg_one (μ ν : Fin 4) (lt : μ < ν) :
    (ReflectionClass.diagonal μ ν lt (-1)).realNormal = basisVec μ - basisVec ν := by
  funext κ
  by_cases h : κ = μ <;> by_cases h' : κ = ν <;>
    simp [ReflectionClass.realNormal, ReflectionClass.intNormal, h, h', lt.ne, lt.ne',
      sub_eq_add_neg]
namespace MirrorPair
variable {a : ℝ} (P : MirrorPair a)
theorem exists_latticeMirror_pair : ∃ Q : LatticeMirror a,
    (Q.cls.realNormal = P.normal ∧ Q.level = P.height) ∨
      (Q.cls.realNormal = -P.normal ∧ Q.level = -P.height) := by
  obtain ⟨n, c, hw⟩ := P
  rcases hw with ⟨⟨μ, rfl⟩, hc⟩ | ⟨⟨μ, κ, hne, hn⟩, q, hq⟩
  · exact ⟨⟨.axial μ, c, hc⟩, Or.inl ⟨realNormal_axial μ, rfl⟩⟩
  · rcases lt_or_gt_of_ne hne with hlt | hlt
    · rcases hn with rfl | rfl
      · exact ⟨⟨.diagonal μ κ hlt 1, c, q, hq⟩, Or.inl ⟨realNormal_diagonal_one μ κ hlt, rfl⟩⟩
      · exact ⟨⟨.diagonal μ κ hlt (-1), c, q, hq⟩,
          Or.inl ⟨realNormal_diagonal_neg_one μ κ hlt, rfl⟩⟩
    · rcases hn with rfl | rfl
      · exact ⟨⟨.diagonal κ μ hlt 1, c, q, hq⟩,
          Or.inl ⟨(realNormal_diagonal_one κ μ hlt).trans (add_comm _ _), rfl⟩⟩
      · refine ⟨⟨.diagonal κ μ hlt (-1), -c, -q, by rw [hq]; push_cast; ring⟩, Or.inr ⟨?_, rfl⟩⟩
        exact (realNormal_diagonal_neg_one κ μ hlt).trans (neg_sub _ _).symm
theorem normal_dotProduct_self_ne_zero : P.normal ⬝ᵥ P.normal ≠ 0 := by
  obtain ⟨Q, ⟨h, -⟩ | ⟨h, -⟩⟩ := P.exists_latticeMirror_pair
  · rw [← h]
    exact Q.cls.realNormal_dot_ne_zero
  · have := Q.cls.realNormal_dot_ne_zero
    rwa [h, neg_dotProduct, dotProduct_neg, neg_neg] at this
theorem exists_latticeMirror_reflect : ∃ Q : LatticeMirror a,
    Q.plane = P.hyperplane ∧
      hyperplaneReflect Q.cls.realNormal Q.level = hyperplaneReflect P.normal P.height ∧
      (∀ H, Q.IsHalfSpace H ↔ H ∈ P.halfSpaces) := by
  obtain ⟨Q, ⟨h, h'⟩ | ⟨h, h'⟩⟩ := P.exists_latticeMirror_pair
  · refine ⟨Q, ?_, by rw [h, h'], fun H => ?_⟩
    · simp [LatticeMirror.plane, hyperplane, h, h']
    · simp [LatticeMirror.IsHalfSpace, halfSpaces, h, h']
  · refine ⟨Q, ?_, by rw [h, h', hyperplaneReflect_neg], fun H => ?_⟩
    · ext x
      simp [LatticeMirror.plane, hyperplane, h, h', neg_dotProduct]
    · simp only [LatticeMirror.IsHalfSpace, halfSpaces, h, h', neg_dotProduct, neg_le_neg_iff,
        mem_insert_iff, mem_singleton_iff]
      exact or_comm
def reflect : LatticeSymmetry a where
  toFun := hyperplaneReflect P.normal P.height
  preservesDist :=
    InfiniteLattice.euclidNormVec_hyperplaneReflect_sub P.normal_dotProduct_self_ne_zero P.height
  image_eq := by
    obtain ⟨Q, -, h, -⟩ := P.exists_latticeMirror_reflect
    rw [← h]
    exact Q.symmetry.image_eq
end MirrorPair
def IsReflectionPositiveAcross {a : ℝ} (ν : Measure (GaugeField a)) (P : MirrorPair a) : Prop :=
  IsProbabilityMeasure ν ∧ ∀ H ∈ P.halfSpaces, ∀ F : GaugeField a → ℂ,
    IsBoundedObservable F → IsLocalObservable F → IsRegionMeasurable H F →
      0 ≤ ∫ U, conj (P.reflect.actOn F U) * F U ∂ν
theorem latticeSymmetry_ext {a : ℝ} {s t : LatticeSymmetry a} (h : s.toFun = t.toFun) :
    s = t := by
  cases s
  cases t
  cases h
  rfl
namespace MirrorPair
variable {a : ℝ} (P : MirrorPair a)
theorem normal_apply_trichotomy (ι : Fin 4) :
    P.normal ι = 0 ∨ P.normal ι = 1 ∨ P.normal ι = -1 := by
  rcases P.admissible with ⟨⟨μ, h⟩, -⟩ | ⟨⟨μ, κ, hne, h | h⟩, -⟩ <;> rw [h]
  · by_cases h1 : ι = μ <;> simp [h1]
  · by_cases h1 : ι = μ <;> by_cases h2 : ι = κ
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp [h1, h2, hne, hne.symm]
  · by_cases h1 : ι = μ <;> by_cases h2 : ι = κ
    · exact absurd (h1.symm.trans h2) hne
    all_goals simp [h1, h2, hne, hne.symm]
theorem eq_or_eq_neg_of_hyperplane_eq (P' : MirrorPair a) (h : P.hyperplane = P'.hyperplane) :
    (P'.normal = P.normal ∧ P'.height = P.height) ∨
      (P'.normal = -P.normal ∧ P'.height = -P.height) := by
  have hN := P.normal_dotProduct_self_ne_zero
  have hN' := P'.normal_dotProduct_self_ne_zero
  set n := P.normal with hn
  set c := P.height with hc
  set n' := P'.normal with hn'
  set c' := P'.height with hc'
  have hmem : ∀ x, n ⬝ᵥ x = c → n' ⬝ᵥ x = c' := fun x hx => by
    have : x ∈ P.hyperplane := hx
    rw [h] at this
    exact this
  set t : ℝ := (n' ⬝ᵥ n) / (n ⬝ᵥ n) with ht
  set v : AmbientSpace := n' - t • n with hv
  set x₀ : AmbientSpace := (c / (n ⬝ᵥ n)) • n with hx₀
  have hx₀c : n ⬝ᵥ x₀ = c := by
    rw [hx₀, dotProduct_smul, smul_eq_mul]
    field_simp
  have hnv : n ⬝ᵥ v = 0 := by
    rw [hv, dotProduct_sub, dotProduct_smul, smul_eq_mul, ht, dotProduct_comm n n']
    field_simp
    ring
  have h1 : n' ⬝ᵥ x₀ = c' := hmem _ hx₀c
  have h2 : n' ⬝ᵥ (x₀ + v) = c' := hmem _ (by rw [dotProduct_add, hx₀c, hnv, add_zero])
  have hn'v : n' ⬝ᵥ v = 0 := by
    rw [dotProduct_add, h1] at h2
    linarith
  have hvv : v ⬝ᵥ v = 0 := by
    have : v ⬝ᵥ v = n' ⬝ᵥ v - t * (n ⬝ᵥ v) := by
      conv_lhs => rw [hv]
      rw [sub_dotProduct, smul_dotProduct, smul_eq_mul]
    rw [this, hn'v, hnv]
    ring
  have hv0 : v = 0 := dotProduct_self_eq_zero.mp hvv
  have hnt : n' = t • n := sub_eq_zero.mp hv0
  have hct : c' = t * c := by
    rw [← h1, hnt, smul_dotProduct, smul_eq_mul, hx₀c]
  have ht0 : t ≠ 0 := by
    intro h0
    apply hN'
    rw [hnt, h0, zero_smul]
    simp
  obtain ⟨ι, hι⟩ : ∃ ι, n ι ≠ 0 := by
    by_contra hcon
    apply hN
    have : n = 0 := funext fun ι => by_contra fun hι => hcon ⟨ι, hι⟩
    rw [this]
    simp
  have hentry : n' ι = t * n ι := by rw [hnt]; rfl
  have ht1 : t = 1 ∨ t = -1 := by
    have e := P.normal_apply_trichotomy ι
    have e' := P'.normal_apply_trichotomy ι
    rw [← hn] at e
    rw [← hn'] at e'
    rcases e with e | e | e
    · exact absurd e hι
    · rw [e, mul_one] at hentry
      rw [hentry] at e'
      rcases e' with e' | e' | e'
      · exact absurd e' ht0
      · exact Or.inl e'
      · exact Or.inr e'
    · rw [e, mul_neg_one] at hentry
      rw [hentry] at e'
      rcases e' with e' | e' | e'
      · exact absurd (neg_eq_zero.mp e') ht0
      · exact Or.inr (neg_eq_iff_eq_neg.mp e')
      · exact Or.inl (neg_injective e')
  rcases ht1 with ht1 | ht1
  · left
    exact ⟨by rw [hnt, ht1, one_smul], by rw [hct, ht1, one_mul]⟩
  · right
    exact ⟨by rw [hnt, ht1, neg_one_smul], by rw [hct, ht1, neg_one_mul]⟩
theorem reflect_eq_of_hyperplane_eq (P' : MirrorPair a) (h : P.hyperplane = P'.hyperplane) :
    P.reflect = P'.reflect := by
  apply latticeSymmetry_ext
  change hyperplaneReflect P.normal P.height = hyperplaneReflect P'.normal P'.height
  rcases P.eq_or_eq_neg_of_hyperplane_eq P' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
  · rw [h1, h2, hyperplaneReflect_neg]
theorem halfSpaces_eq_of_hyperplane_eq (P' : MirrorPair a) (h : P.hyperplane = P'.hyperplane) :
    P.halfSpaces = P'.halfSpaces := by
  rcases P.eq_or_eq_neg_of_hyperplane_eq P' h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [halfSpaces, h1, h2]
  · simp only [halfSpaces, h1, h2, neg_dotProduct, neg_le_neg_iff]
    exact pair_comm _ _
theorem exists_latticeMirror_eq : ∃ Q : LatticeMirror a,
    Q.plane = P.hyperplane ∧ Q.symmetry = P.reflect ∧
      (∀ H, Q.IsHalfSpace H ↔ H ∈ P.halfSpaces) ∧
      ∀ ν : Measure (GaugeField a),
        InfiniteLattice.IsReflectionPositiveAt ν Q ↔ IsReflectionPositiveAcross ν P := by
  obtain ⟨Q, h1, h2, h3⟩ := P.exists_latticeMirror_reflect
  have hr : Q.symmetry = P.reflect := latticeSymmetry_ext h2
  refine ⟨Q, h1, hr, h3, fun ν => ?_⟩
  have hint : ∀ F : GaugeField a → ℂ, ∫ U, F U * Q.conjReflect F U ∂ν =
      ∫ U, conj (P.reflect.actOn F U) * F U ∂ν := fun F => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun U => ?_)
    simp only [LatticeMirror.conjReflect, hr, mul_comm]
  simp only [InfiniteLattice.IsReflectionPositiveAt, IsReflectionPositiveAcross, h3, hint]
end MirrorPair
theorem exists_of_latticeMirror {a : ℝ} (Q : LatticeMirror a) : ∃ P : MirrorPair a,
    P.normal = Q.cls.realNormal ∧ P.height = Q.level ∧ P.hyperplane = Q.plane := by
  obtain ⟨F, c, hc⟩ := Q
  cases F with
  | axial μ =>
    exact ⟨⟨_, c, Or.inl ⟨⟨μ, realNormal_axial μ⟩, hc⟩⟩, rfl, rfl, rfl⟩
  | diagonal μ ν lt s =>
    rcases Int.units_eq_one_or s with rfl | rfl
    · exact ⟨⟨_, c, Or.inr ⟨⟨μ, ν, lt.ne, Or.inl (realNormal_diagonal_one μ ν lt)⟩, hc⟩⟩,
        rfl, rfl, rfl⟩
    · exact ⟨⟨_, c, Or.inr ⟨⟨μ, ν, lt.ne, Or.inr (realNormal_diagonal_neg_one μ ν lt)⟩, hc⟩⟩,
        rfl, rfl, rfl⟩
end YangMills.Construction.ReflectionPositivity.MirrorHyperplanes
