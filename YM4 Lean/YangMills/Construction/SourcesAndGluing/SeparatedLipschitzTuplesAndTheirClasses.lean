import YangMills.Construction.SourcesAndGluing.BallTransportAndInducedIsometries
import Mathlib
set_option autoImplicit false
open Set
open scoped ENNReal
noncomputable section
namespace YangMills.Construction.SourcesAndGluing
inductive Ambient where
  | euclidean
  | torus (m : ℕ+)
namespace Ambient
variable (S : GluingSetup)
abbrev Pt : Ambient → Type
  | euclidean => Fin 4 → ℝ
  | torus m => S.torusAt m
def metric : (X : Ambient) → X.Pt S → X.Pt S → ℝ
  | euclidean, x, y => TestFunctions.euclidDistR4 x y
  | torus _, u, v => TestFunctions.euclidDistTorus u v
def setMetric : (X : Ambient) → Set (X.Pt S) → Set (X.Pt S) → ℝ≥0∞
  | euclidean, A, B => TestFunctions.setDistR4 A B
  | torus _, A, B => TorusMetric.setEuclidDist A B
def supp : (X : Ambient) → (X.Pt S → ℝ) → Set (X.Pt S)
  | euclidean, f => GluingSetup.suppR4 f
  | torus m, f => (S.withCutoffAndSide S.K m).suppTorus f
def IsCompactIn : (X : Ambient) → Set (X.Pt S) → Prop
  | euclidean, A => IsCompact A
  | torus _, A => IsCompact A
def IsC1 : (X : Ambient) → (X.Pt S → ℝ) → Prop
  | euclidean, f => TestFunctions.IsC1R4 f
  | torus m, f => (S.withCutoffAndSide S.K m).IsC1 f
def ball : (X : Ambient) → X.Pt S → ℝ → Set (X.Pt S)
  | euclidean, x, R => closedBallAt x R
  | torus _, u, R => TestFunctions.closedBallTorus u R
abbrev FunTuple (X : Ambient) (n : ℕ+) : Type := Fin n → X.Pt S → ℝ
variable {S}
def CompactDisjointSupp (X : Ambient) {n : ℕ+} (f : X.FunTuple S n) : Prop :=
  (∀ i, X.IsCompactIn S (X.supp S (f i))) ∧
    ∀ i j, i ≠ j → Disjoint (X.supp S (f i)) (X.supp S (f j))
def IsSepLip (X : Ambient) {n : ℕ+} (f : X.FunTuple S n) : Prop :=
  (∀ i, TestFunctions.IsLipschitzFor (X.metric S) (f i)) ∧ X.CompactDisjointSupp f
def SuppSubset (X : Ambient) {n : ℕ+} (f : X.FunTuple S n) (U : Set (X.Pt S)) : Prop :=
  ∀ i, X.supp S (f i) ⊆ U
def minGap (X : Ambient) {n : ℕ+} (f : X.FunTuple S n) : ℝ≥0∞ :=
  ⨅ i, ⨅ j, ⨅ _ : i ≠ j, X.setMetric S (X.supp S (f i)) (X.supp S (f j))
end Ambient
def restrictLength {n : ℕ+} (I : Finset (Fin n)) (hI : I.Nonempty) : ℕ+ :=
  ⟨I.card, hI.card_pos⟩
def restrictTuple {α : Type*} {n : ℕ+} (f : Fin n → α) (I : Finset (Fin n)) (hI : I.Nonempty) :
    Fin (restrictLength I hI) → α :=
  fun j => f (I.orderEmbOfFin (k := restrictLength I hI) rfl j)
namespace Ambient
variable (S : GluingSetup)
def sepC1 (X : Ambient) (n : ℕ+) : Set (X.FunTuple S n) :=
  {f | (∀ i, X.IsC1 S (f i)) ∧ X.CompactDisjointSupp f}
def sepC1Ball (n : ℕ+) (ρ : ℝ) : Set (euclidean.FunTuple S n) :=
  {f | f ∈ euclidean.sepC1 S n ∧ euclidean.SuppSubset f (ballR4 ρ)}
def lipClass (X : Ambient) (n : ℕ+) (d R : ℝ) : Set (X.FunTuple S n) :=
  {f | (∀ i, TestFunctions.IsLipschitzFor (X.metric S) (f i)) ∧
    (∀ i, ∃ x, X.supp S (f i) ⊆ X.ball S x R) ∧
    ∀ i j, i ≠ j →
      ENNReal.ofReal d ≤ X.setMetric S (X.supp S (f i)) (X.supp S (f j))}
def IsMultilinearOn {n : ℕ+} (m : ℕ+) (T : Set (euclidean.FunTuple S n))
    (Φ : euclidean.FunTuple S n → (torus m).FunTuple S n) : Prop :=
  ∀ (i : Fin n) (α β : ℝ), ∀ f ∈ T, ∀ g ∈ T, ∀ h ∈ T,
    (∀ j, j ≠ i → f j = g j ∧ f j = h j) → h i = α • f i + β • g i →
      (∀ j, j ≠ i → Φ f j = Φ g j ∧ Φ f j = Φ h j) ∧ Φ h i = α • Φ f i + β • Φ g i
end Ambient
end YangMills.Construction.SourcesAndGluing
end
