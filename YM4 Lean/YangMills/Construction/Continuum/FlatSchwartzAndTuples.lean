import YangMills.Construction.Continuum.DiagonalFlatSchwartz
import YangMills.Construction.Lattice.ObservablesAndTestNorms
import Mathlib
set_option autoImplicit false
open Set
open scoped ContDiff ENNReal
noncomputable section
namespace YangMills.Construction.EuclideanCoords
variable {D : ℕ}
def sqrtSumSq (x : Fin D → ℝ) : ℝ := Real.sqrt (∑ ι, x ι ^ 2)
def supCoord (x : Fin D → ℝ) : ℝ := ⨆ ι, |x ι|
end YangMills.Construction.EuclideanCoords
namespace YangMills.Construction.SmoothMaps
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
def smoothSet : Set (V → ℂ) := {f | ContDiff ℝ ∞ f}
def smoothCompactSet : Set (V → ℂ) := {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f}
variable {V}
def IsRealValued {X : Type*} (f : X → ℂ) : Prop := ∀ x, (f x).im = 0
end YangMills.Construction.SmoothMaps

namespace YangMills.Construction.EuclideanBalls
def euclidBall {k : ℕ} (x : Fin k → ℝ) (ρ : ℝ) : Set (Fin k → ℝ) :=
  {z | EuclideanCoords.sqrtSumSq (z - x) < ρ}
def compactC1 (k : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Set ((Fin k → ℝ) → F) :=
  {f | ContDiff ℝ 1 f ∧ HasCompactSupport f}
end YangMills.Construction.EuclideanBalls

namespace YangMills.Construction.ConfigSpace
open YangMills.Construction.SmoothMaps YangMills.Construction.TestFunctions
variable {n : ℕ}
def cylinderSet (S : Fin n → Set (Fin 4 → ℝ)) : Set (Config n) := {x | ∀ i, x i ∈ S i}
def coordSupNorm (x : Config n) : ℝ := ⨆ i, ⨆ c, |x i c|
def gradNorm (φ : (Fin 4 → ℝ) → ℂ) (y : Fin 4 → ℝ) : ℝ :=
  Real.sqrt (∑ c, ‖partialDerivR4 c φ y‖ ^ 2)
def gradSupNorm (φ : (Fin 4 → ℝ) → ℂ) : ℝ := ⨆ y, gradNorm φ y
def IsClosedBallRadius (B : Set (Fin 4 → ℝ)) (ϱ : ℝ) : Prop := ∃ a, B = closedBallR4 a ϱ
def schwartzSet (n : ℕ) : Set (Config n → ℂ) :=
  {φ | ContDiff ℝ ∞ φ ∧ ∀ (k : ℕ) (α : MultiIndex n),
    (⨆ x, ENNReal.ofReal ((1 + euclidNorm x) ^ k * ‖iteratedPartial α φ x‖)) < ⊤}
def flatSchwartzSet (n : ℕ) : Set (Config n → ℂ) :=
  {φ | φ ∈ schwartzSet n ∧
    ∀ (α : MultiIndex n), ∀ x ∈ diagonalSet n, iteratedPartial α φ x = 0}
def IsLinearOnFlat (S : flatSchwartzSet n → ℂ) : Prop :=
  (∀ φ ψ χ : flatSchwartzSet n, χ.1 = φ.1 + ψ.1 → S χ = S φ + S ψ) ∧
    ∀ (lam : ℂ) (φ χ : flatSchwartzSet n), χ.1 = lam • φ.1 → S χ = lam * S φ
def flatDualSet (n : ℕ) : Set (flatSchwartzSet n → ℂ) :=
  {S | IsLinearOnFlat S ∧ ∃ (k q : ℕ) (b : ℝ), 0 ≤ b ∧ ∀ φ : flatSchwartzSet n,
    ENNReal.ofReal ‖S φ‖ ≤ ENNReal.ofReal b * decaySeminorm k q φ.1}
def testFnOffDiag (n : ℕ) : Set (Config n → ℂ) :=
  {f | ContDiff ℝ ∞ f ∧ HasCompactSupport f ∧ tsupport f ⊆ injectiveTuples (Fin 4 → ℝ) n}
def IsSchwartzDenseIn (A B : Set (Config n → ℂ)) : Prop :=
  A ⊆ B ∧ B ⊆ schwartzSet n ∧ ∀ f ∈ B, ∀ (k l : ℕ) (ε : ℝ), 0 < ε →
    ∃ g ∈ A, decaySeminorm k l (f - g) < ENNReal.ofReal ε
abbrev FnTuple (n : ℕ) : Type := Fin n → (Fin 4 → ℝ) → ℂ
def tensorProd {E : Type*} [CommMonoid E] (f : Fin n → (Fin 4 → ℝ) → E) : Config n → E :=
  fun x => ∏ i, f i (x i)
def c1CompactIn (O : Set (Fin 4 → ℝ)) : Set ((Fin 4 → ℝ) → ℂ) :=
  {f | ContDiff ℝ 1 f ∧ HasCompactSupport f ∧ tsupport f ⊆ O}
def DisjointSupports (f : FnTuple n) : Prop :=
  ∀ i i', i ≠ i' → Disjoint (tsupport (f i)) (tsupport (f i'))
def realTupleSet (n : ℕ) (O : Set (Fin 4 → ℝ)) : Set (FnTuple n) :=
  {f | (∀ i, IsRealValued (f i) ∧ f i ∈ c1CompactIn O) ∧ DisjointSupports f}
def SmoothEntries (f : FnTuple n) : Prop := ∀ i, ContDiff ℝ ∞ (f i)
def smoothRealTupleSet (n : ℕ) : Set (FnTuple n) :=
  {f | f ∈ realTupleSet n univ ∧ SmoothEntries f}
def smoothComplexTupleSet (n : ℕ) : Set (FnTuple n) :=
  {f | (∀ i, f i ∈ smoothCompactSet (Fin 4 → ℝ)) ∧ DisjointSupports f}
def AgreeExcept (i : Fin n) (h h' : FnTuple n) : Prop := ∀ k, k ≠ i → h k = h' k
def IsRealMultilinearSmooth (T : smoothRealTupleSet n → ℝ) : Prop :=
  ∀ (i : Fin n) (h h' : smoothRealTupleSet n), AgreeExcept i h.1 h'.1 →
    (∀ s : smoothRealTupleSet n, s.1 = Function.update h.1 i (h.1 i + h'.1 i) →
      T s = T h + T h') ∧
    ∀ (lam : ℝ) (s : smoothRealTupleSet n),
      s.1 = Function.update h.1 i ((lam : ℂ) • h.1 i) → T s = lam * T h
def IsComplexMultilinearSmooth (T : smoothComplexTupleSet n → ℂ) : Prop :=
  ∀ (i : Fin n) (h h' : smoothComplexTupleSet n), AgreeExcept i h.1 h'.1 →
    (∀ s : smoothComplexTupleSet n, s.1 = Function.update h.1 i (h.1 i + h'.1 i) →
      T s = T h + T h') ∧
    ∀ (lam : ℂ) (s : smoothComplexTupleSet n),
      s.1 = Function.update h.1 i (lam • h.1 i) → T s = lam * T h
def IsRealMultilinear (Φ : realTupleSet n univ → ℝ) : Prop :=
  ∀ (i : Fin n) (b b' : ℝ) (X X' X'' : realTupleSet n univ), AgreeExcept i X.1 X'.1 →
    X''.1 = Function.update X.1 i ((b : ℂ) • X.1 i + (b' : ℂ) • X'.1 i) →
    Φ X'' = b * Φ X + b' * Φ X'
end YangMills.Construction.ConfigSpace
