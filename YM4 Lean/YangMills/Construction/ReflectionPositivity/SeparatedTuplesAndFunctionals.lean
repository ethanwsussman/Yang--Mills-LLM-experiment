import YangMills.Construction.ReflectionPositivity.FunctionsOfClassC1AndSupports
import YangMills.Construction.ReflectionPositivity.ReflectionsHyperplanesMirrorsAndOpenSides
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace Ambient
variable (D : MirrorData) (E : Ambient)
abbrev FnList : Type := List (E.Point D → ℝ)
def IsSeparatedList (X : FnList D E) : Prop :=
  (∀ f ∈ X, f ∈ compactC1 D ℝ E) ∧
    X.Pairwise fun f g => Disjoint (closedSupport D E f) (closedSupport D E g)
def separatedN (n : ℕ) : Set (FnList D E) := {X | X.length = n ∧ IsSeparatedList D E X}
def separatedAll : Set (FnList D E) := ⋃ n, separatedN D E n
def separatedWithin (O : Set (E.Point D)) : Set (FnList D E) :=
  {X | X ∈ separatedAll D E ∧ ∀ f ∈ X, closedSupport D E f ⊆ O}
theorem separatedN_zero : separatedN D E 0 = {[]} := by
  ext X
  constructor
  · rintro ⟨hlen, -⟩
    exact List.length_eq_zero_iff.1 hlen
  · rintro rfl
    exact ⟨rfl, by simp [IsSeparatedList]⟩
theorem separatedN_subset_separatedAll (n : ℕ) :
    separatedN D E n ⊆ separatedAll D E :=
  Set.subset_iUnion (separatedN D E) n
theorem nil_mem_separatedWithin (O : Set (E.Point D)) : [] ∈ separatedWithin D E O :=
  ⟨separatedN_subset_separatedAll D E 0 (by simp [separatedN_zero]), by simp⟩
def emptyList : separatedAll D E :=
  ⟨[], separatedN_subset_separatedAll D E 0 (by simp [separatedN_zero])⟩
variable {D E} in
def evalOrZero {A : Set (FnList D E)} (φ : A → ℝ) (X : FnList D E) : ℝ :=
  open Classical in if hX : X ∈ A then φ ⟨X, hX⟩ else 0
def setDist : (E : Ambient) → Set (E.Point D) → Set (E.Point D) → ℝ≥0∞
  | torus, A, B => YangMills.Construction.TorusMetric.setEuclidDist
      (S := YangMills.Construction.PeriodicLattice.torusSide D.L D.m) A B
  | euclidean, A, B => ⨅ a ∈ A, ⨅ b ∈ B, ENNReal.ofReal (metric D euclidean a b)
theorem disjoint_of_setDist_pos {A B : Set (E.Point D)} (hpos : 0 < setDist D E A B) :
    Disjoint A B := by
  rw [Set.disjoint_left]
  intro x hA hB
  have hle : setDist D E A B ≤ ENNReal.ofReal (metric D E x x) := by
    cases E with
    | torus => exact iInf₂_le_of_le x hA (iInf₂_le x hB)
    | euclidean => exact iInf₂_le_of_le x hA (iInf₂_le x hB)
  have hself : metric D E x x ≤ 0 := by
    cases E with
    | torus =>
      have hz : ∀ y : D.Torus, YangMills.Construction.TorusMetric.torusEuclidNorm (y - y) ≤ 0 :=
        fun y => by
          refine csInf_le ⟨0, ?_⟩ ⟨0, ?_, ?_⟩
          · rintro _ ⟨v, -, rfl⟩
            exact Real.sqrt_nonneg _
          · simp only [Set.mem_preimage, Set.mem_singleton_iff, sub_self]
            funext μ
            simp [YangMills.Construction.TorusMetric.torusProj]
          · simp [YangMills.Construction.TorusMetric.euclidNormVec]
      exact hz x
    | euclidean =>
      have hz : ∀ y : Fin 4 → ℝ, YangMills.Construction.TorusMetric.euclidNormVec (y - y) ≤ 0 :=
        fun y => by
          simp [YangMills.Construction.TorusMetric.euclidNormVec]
      exact hz x
  rw [ENNReal.ofReal_eq_zero.2 hself] at hle
  exact absurd hpos (not_lt.2 hle)
def compactC1SuppIn (A : Set (E.Point D)) : Set (E.Point D → ℝ) :=
  {f | f ∈ compactC1 D ℝ E ∧ closedSupport D E f ⊆ A}
theorem ofFn_mem_separatedN {n : ℕ} {A : Fin n → Set (E.Point D)}
    (hA : Pairwise fun i j => 0 < setDist D E (A i) (A j)) {f : Fin n → E.Point D → ℝ}
    (hf : ∀ i, f i ∈ compactC1SuppIn D E (A i)) : List.ofFn f ∈ separatedN D E n := by
  refine ⟨List.length_ofFn, ?_, ?_⟩
  · intro g hg
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hg
    exact (hf i).1
  · rw [List.pairwise_ofFn]
    intro i j hij
    exact (disjoint_of_setDist_pos D E (hA hij.ne)).mono (hf i).2 (hf j).2
def IsSeparatedMultilinear {n : ℕ} (φ : separatedN D E n → ℝ) : Prop :=
  ∀ A : Fin n → Set (E.Point D), (Pairwise fun i j => 0 < setDist D E (A i) (A j)) →
    ∀ f : Fin n → E.Point D → ℝ, (∀ i, f i ∈ compactC1SuppIn D E (A i)) →
      ∀ (i : Fin n) (g : E.Point D → ℝ), g ∈ compactC1SuppIn D E (A i) → ∀ s t : ℝ,
        evalOrZero φ (List.ofFn (Function.update f i (s • f i + t • g))) =
          s * evalOrZero φ (List.ofFn f) + t * evalOrZero φ (List.ofFn (Function.update f i g))
def restrictN (σ : separatedAll D E → ℝ) (n : ℕ) : separatedN D E n → ℝ :=
  σ ∘ Set.inclusion (separatedN_subset_separatedAll D E n)
def IsSeparatedFunctional (σ : separatedAll D E → ℝ) : Prop :=
  σ (emptyList D E) = 1 ∧ ∀ n, 1 ≤ n → IsSeparatedMultilinear D E (restrictN D E σ n)
structure ConnectedFamily where
  fn : (n : ℕ) → 2 ≤ n → separatedN D E n → ℝ
  fn_multilinear : ∀ n (hn : 2 ≤ n), IsSeparatedMultilinear D E (fn n hn)
variable {D E}
def append {α : Type*} (X Y : List (E.Point D → α)) : List (E.Point D → α) := X ++ Y
end Ambient
namespace CoordMirror
variable (D : MirrorData) (S : CoordMirror) (E : Ambient) {α : Type*}
def reflectList (X : List (E.Point D → α)) : List (E.Point D → α) :=
  X.map (S.pullback D E)
def reflectAppend (X Y : List (E.Point D → α)) : List (E.Point D → α) :=
  Ambient.append (S.reflectList D E X) Y
end CoordMirror
end YangMills.Construction.ReflectionPositivity.AxisMirror
