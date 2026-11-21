import YangMills.Construction.Cumulants.NonSingletonPartitions
import YangMills.Construction.PassageToTheLimit.SpaceTestFunctionsTranslationsReflectionsPositions
import Mathlib
set_option autoImplicit false
open Set
noncomputable section
namespace YangMills.Construction
namespace LimitSpaces
inductive TestKind where
  | lip
  | cOne
namespace Ambient
variable (s : Conventions.StandingParameters) (E : Ambient)
def SupportedWithin {Z : Type*} [Zero Z] (A : Set (E.Carrier s)) (f : E.Carrier s → Z) : Prop :=
  E.IsCompactSubset s (E.closedSupport s f) ∧ E.closedSupport s f ⊆ A
def lipWithin (A : Set (E.Carrier s)) : Set (E.Carrier s → ℝ) :=
  {f | E.IsLip s f ∧ E.SupportedWithin s A f}
def c1Within (A : Set (E.Carrier s)) : Set (E.Carrier s → ℝ) :=
  {f | f ∈ E.c1Compact s ∧ E.SupportedWithin s A f}
def testWithin : TestKind → Set (E.Carrier s) → Set (E.Carrier s → ℝ)
  | .lip, A => E.lipWithin s A
  | .cOne, A => E.c1Within s A
variable {n : ℕ}
def IsSepLipTuple (D : Set (E.Carrier s)) (f : Fin n → E.Carrier s → ℝ) : Prop :=
  (∀ i, f i ∈ E.lipWithin s D) ∧
    Pairwise fun i j => Disjoint (E.closedSupport s (f i)) (E.closedSupport s (f j))
def IsSepC1Tuple (D : Set (E.Carrier s)) (f : Fin n → E.Carrier s → ℝ) : Prop :=
  E.IsSepLipTuple s D f ∧ ∀ i, f i ∈ E.c1Compact s
def IsSepTuple : TestKind → Set (E.Carrier s) → (Fin n → E.Carrier s → ℝ) → Prop
  | .lip, D, f => E.IsSepLipTuple s D f
  | .cOne, D, f => E.IsSepC1Tuple s D f
abbrev SepTuple (k : TestKind) (D : Set (E.Carrier s)) (n : ℕ) : Type :=
  {f : Fin n → E.Carrier s → ℝ // E.IsSepTuple s k D f}
abbrev SepTupleUniv (k : TestKind) (n : ℕ) : Type :=
  E.SepTuple s k univ n
theorem IsSepTuple.comp_inj {E : Ambient} {s : Conventions.StandingParameters} {k : TestKind}
    {D : Set (E.Carrier s)} {m : ℕ} {f : Fin n → E.Carrier s → ℝ} (h : E.IsSepTuple s k D f)
    {e : Fin m → Fin n} (he : Function.Injective e) : E.IsSepTuple s k D (f ∘ e) := by
  have hl : ∀ {g : Fin n → E.Carrier s → ℝ}, E.IsSepLipTuple s D g →
      E.IsSepLipTuple s D (g ∘ e) :=
    fun hg => ⟨fun i => hg.1 (e i), fun _ _ hij => hg.2 (he.ne hij)⟩
  cases k with
  | lip => exact hl h
  | cOne => exact ⟨hl h.1, fun i => h.2 (e i)⟩
def pickComponents {Z : Type*} (f : Fin n → Z) (J : Finset (Fin n)) : Fin J.card → Z :=
  f ∘ J.orderEmbOfFin rfl
variable {k : TestKind} {D : Set (E.Carrier s)}
def restrictTuple (X : E.SepTuple s k D n) (J : Finset (Fin n)) :
    E.SepTuple s k D J.card :=
  ⟨pickComponents X.1 J, IsSepTuple.comp_inj X.2 (J.orderEmbOfFin rfl).injective⟩
def permuteTuple (X : E.SepTuple s k D n) (ς : Equiv.Perm (Fin n)) :
    E.SepTuple s k D n :=
  ⟨X.1 ∘ ς, IsSepTuple.comp_inj X.2 ς.injective⟩
def IsMultilinearOn (Ψ : E.SepTuple s k D n → ℝ) : Prop :=
  ∀ A : Fin n → Set (E.Carrier s), (∀ i, A i ⊆ D) →
    (Pairwise fun i j => E.PositivelySeparated s (A i) (A j)) →
    ∀ (i : Fin n) (a b : ℝ) (X Y Z : E.SepTuple s k D n),
      (∀ j, X.1 j ∈ E.testWithin s k (A j)) → (∀ j, Y.1 j ∈ E.testWithin s k (A j)) →
      (∀ j, Z.1 j ∈ E.testWithin s k (A j)) →
      (∀ j, j ≠ i → Y.1 j = X.1 j) → (∀ j, j ≠ i → Z.1 j = X.1 j) →
      Z.1 i = a • X.1 i + b • Y.1 i → Ψ Z = a * Ψ X + b * Ψ Y
def IsPermInvariant (Ψ : E.SepTuple s k D n → ℝ) : Prop :=
  ∀ (X : E.SepTuple s k D n) (ς : Equiv.Perm (Fin n)), Ψ (E.permuteTuple s X ς) = Ψ X
abbrev TupleFunctionals (k : TestKind) (D : Set (E.Carrier s)) : Type :=
  (n : ℕ) → 2 ≤ n → E.SepTuple s k D n → ℝ
theorem two_le_card_of_mem_nonSingleton {q : ℕ}
    (π : {π // π ∈ SetPartition.nonSingletonPartitions q}) (J : {J // J ∈ π.1.parts}) :
    2 ≤ J.1.card :=
  (Finset.mem_filter.mp π.2).2 J.1 J.2
def centredSum (Ψ : E.TupleFunctionals s k D) {q : ℕ} (X : E.SepTuple s k D q) : ℝ :=
  ∑ π ∈ (SetPartition.nonSingletonPartitions q).attach, ∏ J ∈ π.1.parts.attach,
    Ψ J.1.card (two_le_card_of_mem_nonSingleton π J) (E.restrictTuple s X J.1)
def tensorProd {𝕜 : Type*} [RCLike 𝕜] {q : ℕ} (f : Fin q → E.Carrier s → 𝕜)
    (x : Fin q → E.Carrier s) : 𝕜 :=
  ∏ l, f l (x l)
end Ambient
end LimitSpaces
end YangMills.Construction
end
