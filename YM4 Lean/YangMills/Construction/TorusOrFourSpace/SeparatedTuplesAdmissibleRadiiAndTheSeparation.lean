import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import YangMills.Construction.TorusOrFourSpace.OriginClosedBallsAndBallsAboutTheOrigin
import Mathlib
set_option autoImplicit false
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (P : Params) (K : Kind)
abbrev FnTuple (n : ℕ) : Type := Fin n → K.Pt P → ℝ
def CompactDisjointSupports {n : ℕ} (f : FnTuple P K n) : Prop :=
  (∀ i, IsCompactQ P K (supportQ P K (f i))) ∧
    ∀ i j, i ≠ j → Disjoint (supportQ P K (f i)) (supportQ P K (f j))
def sepC1Tuples (n : ℕ) : Set (FnTuple P K n) :=
  {f | (∀ i, IsC1Fn P K (f i)) ∧ CompactDisjointSupports P K f}
def sepLipTuples (n : ℕ) : Set (FnTuple P K n) :=
  {f | (∀ i, IsLipschitzQ P K (f i)) ∧ CompactDisjointSupports P K f}
def sepC1TuplesWithin (n : ℕ) (O : Set (K.Pt P)) : Set (FnTuple P K n) :=
  {f | f ∈ sepC1Tuples P K n ∧ ∀ i, supportQ P K (f i) ⊆ O}
def sepLipTuplesWithin (n : ℕ) (O : Set (K.Pt P)) : Set (FnTuple P K n) :=
  {f | f ∈ sepLipTuples P K n ∧ ∀ i, supportQ P K (f i) ⊆ O}
def allowedRadii : Kind → Set ℝ
  | .euclidean => Set.Ioi 0
  | .torus => Set.Ioo 0 (P.side / 4)
def lipTuplesSpacedInBalls (n : ℕ) (d R : ℝ) : Set (FnTuple P K n) :=
  {f | (∀ i, IsLipschitzQ P K (f i)) ∧
    (∀ i, ∃ B, IsClosedBallWithRadius P K B R ∧ supportQ P K (f i) ⊆ B) ∧
    ∀ i j, i ≠ j →
      ENNReal.ofReal d ≤ setInfDist P K (supportQ P K (f i)) (supportQ P K (f j))}
def supportGap {n : ℕ} (g : FnTuple P K n) : ℝ≥0∞ :=
  ⨅ i, ⨅ j, ⨅ _ : i ≠ j, setInfDist P K (supportQ P K (g i)) (supportQ P K (g j))
def restrictTuple {n : ℕ} (f : FnTuple P K n) (J : Finset (Fin n)) : FnTuple P K J.card :=
  fun j => f (J.orderEmbOfFin rfl j)
def SupportsDisjoint {n m : ℕ} (f : FnTuple P K n) (g : FnTuple P K m) : Prop :=
  ∀ i j, Disjoint (supportQ P K (f i)) (supportQ P K (g j))
def appendTuples {n m : ℕ} (f : FnTuple P K n) (g : FnTuple P K m) : FnTuple P K (n + m) :=
  Fin.append f g
end YangMills.Construction.PeriodicSpace.Kind
