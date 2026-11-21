import Mathlib
set_option autoImplicit false
open scoped NNReal Topology
noncomputable section
namespace YangMills.Construction
namespace FamilyTopology
universe u v
section Notions
variable {S : Type u}
def IsCompactViaCovers (T : TopologicalSpace S) : Prop :=
  ∀ 𝒰 : Set (Set S), (∀ U ∈ 𝒰, IsOpen[T] U) → ⋃₀ 𝒰 = Set.univ →
    ∃ 𝒱 : Set (Set S), 𝒱 ⊆ 𝒰 ∧ 𝒱.Finite ∧ ⋃₀ 𝒱 = Set.univ
structure IsMetricFunction (d : S → S → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ d x y
  eq_zero_iff : ∀ x y, d x y = 0 ↔ x = y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x z ≤ d x y + d y z
def openBallOf (d : S → S → ℝ) (x : S) (r : ℝ) : Set S := {y | d x y < r}
def IsUnionOfBalls (d : S → S → ℝ) (U : Set S) : Prop :=
  ∃ ℬ : Set (Set S), (∀ B ∈ ℬ, ∃ x, ∃ r : ℝ, 0 < r ∧ B = openBallOf d x r) ∧ U = ⋃₀ ℬ
def IsMetrizableVia (T : TopologicalSpace S) : Prop :=
  ∃ d : S → S → ℝ, IsMetricFunction d ∧ ∀ U, IsOpen[T] U ↔ IsUnionOfBalls d U
def TendstoAlong (T : TopologicalSpace S) (J : Set ℕ+) (_hJ : J.Infinite) (x : J → S) (y : S) :
    Prop :=
  ∀ U, IsOpen[T] U → y ∈ U → ∃ n : ℤ, ∀ j : J, n ≤ (((j : ℕ+) : ℕ) : ℤ) → x j ∈ U
end Notions
section Family
variable {X : Type u} {𝔄 : Type v}
def IsBasicOpen (e : 𝔄 → X → ℝ) (B : Set X) : Prop :=
  ∃ (t : ℕ) (a : Fin t → 𝔄) (O : Fin t → Set ℝ),
    (∀ i, IsOpen (O i)) ∧ B = {x | ∀ i, e (a i) x ∈ O i}
def familyOpens (e : 𝔄 → X → ℝ) : Set (Set X) :=
  {U | ∃ ℬ : Set (Set X), (∀ B ∈ ℬ, IsBasicOpen e B) ∧ U = ⋃₀ ℬ}
theorem IsBasicOpen.inter {e : 𝔄 → X → ℝ} {B C : Set X} (hB : IsBasicOpen e B)
    (hC : IsBasicOpen e C) : IsBasicOpen e (B ∩ C) := by
  obtain ⟨t, a, O, hO, rfl⟩ := hB
  obtain ⟨t', a', O', hO', rfl⟩ := hC
  refine ⟨t + t', Fin.append a a', Fin.append O O', ?_, ?_⟩
  · intro i
    induction i using Fin.addCases with
    | left i => simpa using hO i
    | right i => simpa using hO' i
  · ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Fin.forall_fin_add, Fin.append_left,
      Fin.append_right]
@[instance_reducible] def familyTopology (e : 𝔄 → X → ℝ) : TopologicalSpace X where
  IsOpen U := U ∈ familyOpens e
  isOpen_univ := ⟨{Set.univ}, by
    rintro B rfl
    exact ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by ext x; simp⟩, by simp⟩
  isOpen_inter := by
    rintro _ _ ⟨ℬ, hℬ, rfl⟩ ⟨𝒞, h𝒞, rfl⟩
    refine ⟨Set.image2 (· ∩ ·) ℬ 𝒞, ?_, ?_⟩
    · rintro _ ⟨B, hB, C, hC, rfl⟩
      exact (hℬ B hB).inter (h𝒞 C hC)
    · ext x
      simp only [Set.mem_inter_iff, Set.mem_sUnion, Set.mem_image2]
      constructor
      · rintro ⟨⟨B, hB, hxB⟩, C, hC, hxC⟩
        exact ⟨B ∩ C, ⟨B, hB, C, hC, rfl⟩, hxB, hxC⟩
      · rintro ⟨_, ⟨B, hB, C, hC, rfl⟩, hxB, hxC⟩
        exact ⟨⟨B, hB, hxB⟩, C, hC, hxC⟩
  isOpen_sUnion := by
    intro 𝒮 h𝒮
    refine ⟨{B | IsBasicOpen e B ∧ ∃ U ∈ 𝒮, B ⊆ U}, fun B hB => hB.1, ?_⟩
    ext x
    simp only [Set.mem_sUnion, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨U, hU, hxU⟩
      obtain ⟨ℬ, hℬ, rfl⟩ := h𝒮 U hU
      obtain ⟨B, hB, hxB⟩ := hxU
      exact ⟨B, ⟨hℬ B hB, _, hU, Set.subset_sUnion_of_mem hB⟩, hxB⟩
    · rintro ⟨B, ⟨-, U, hU, hBU⟩, hxB⟩
      exact ⟨U, hU, hBU hxB⟩
def SeparatesPoints (e : 𝔄 → X → ℝ) : Prop :=
  ∀ x x' : X, x ≠ x' → ∃ α, e α x ≠ e α x'
def familyDistance (e : 𝔄 → X → ℝ) (α : ℕ+ → 𝔄) (_hα : Function.Surjective α) (x x' : X) : ℝ :=
  ∑' s : ℕ+, (2 : ℝ) ^ (-((s : ℕ) : ℤ)) * min 1 |e (α s) x - e (α s) x'|
end Family
section Products
variable {𝔄 : Type v}
def intervalBox (c : 𝔄 → ℝ≥0) : Set (𝔄 → ℝ) := {p | ∀ α, |p α| ≤ c α}
def boxCoord (c : 𝔄 → ℝ≥0) (α : 𝔄) (p : intervalBox c) : ℝ := p.1 α
@[instance_reducible] def boxTopology (c : 𝔄 → ℝ≥0) :
    TopologicalSpace (intervalBox c) :=
  familyTopology (boxCoord c)
end Products
end FamilyTopology
end YangMills.Construction
