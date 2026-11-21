import YangMills.Construction.GrowingTori.DefinitionsForSequencesOfGrowingTori
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.GrowingTori.Ambient
variable {L : ℕ} (E : Ambient L)
@[reducible] def topology : TopologicalSpace E.Point where
  IsOpen U := ∀ u ∈ U, ∃ ε : ℝ, 0 < ε ∧ ∀ v, E.separation u v < ε → v ∈ U
  isOpen_univ := fun _ _ => ⟨1, one_pos, fun _ _ => mem_univ _⟩
  isOpen_inter := by
    intro s t hs ht u hu
    obtain ⟨a, ha, h⟩ := hs u hu.1
    obtain ⟨b, hb, h'⟩ := ht u hu.2
    exact ⟨min a b, lt_min ha hb, fun v hv =>
      ⟨h v (lt_of_lt_of_le hv (min_le_left _ _)), h' v (lt_of_lt_of_le hv (min_le_right _ _))⟩⟩
  isOpen_sUnion := by
    rintro s hs u ⟨t, ht, hu⟩
    obtain ⟨a, ha, h⟩ := hs t ht u hu
    exact ⟨a, ha, fun v hv => ⟨t, ht, h v hv⟩⟩
def IsEuclidCompact (A : Set E.Point) : Prop := @IsCompact _ E.topology A
def euclidClosure (A : Set E.Point) : Set E.Point := @closure _ E.topology A
def setDist : (E : Ambient L) → Set E.Point → Set E.Point → ℝ≥0∞
  | euclidean => fun (A B : Set (Fin 4 → ℝ)) => TestFunctions.setDistR4 A B
  | torus ℓ _ => fun (A B : Set (TorusMetric.Torus4 ℓ)) => TorusMetric.setEuclidDist A B
def supp {V : Type*} [Zero V] (f : E.Point → V) : Set E.Point :=
  E.euclidClosure {u | f u ≠ 0}
def closedBall (u : E.Point) (R : ℝ) : Set E.Point := {v | E.separation v u ≤ R}
def IsClosedBallOf (R : ℝ) (A : Set E.Point) : Prop := 0 < R ∧ ∃ u, A = E.closedBall u R
def lipCompact (A : Set E.Point) : Set (E.Point → ℝ) :=
  {f | TestFunctions.IsLipschitzFor E.separation f ∧ E.IsEuclidCompact (E.supp f) ∧ E.supp f ⊆ A}
def PairwiseDisjointSupp {V : Type*} [Zero V] {n : ℕ} (f : Fin n → E.Point → V) : Prop :=
  ∀ i k, i ≠ k → Disjoint (E.supp (f i)) (E.supp (f k))
def IsSeparatedLipTuple {n : ℕ} (f : Fin n → E.Point → ℝ) : Prop :=
  1 ≤ n ∧ (∀ i, f i ∈ E.lipCompact univ) ∧ E.PairwiseDisjointSupp f
def IsRSupported {V : Type*} [Zero V] {n : ℕ} (R : ℝ) (f : Fin n → E.Point → V) : Prop :=
  0 < R ∧ ∀ i, ∃ B, E.IsClosedBallOf R B ∧ E.supp (f i) ⊆ B
end YangMills.Construction.GrowingTori.Ambient
end
