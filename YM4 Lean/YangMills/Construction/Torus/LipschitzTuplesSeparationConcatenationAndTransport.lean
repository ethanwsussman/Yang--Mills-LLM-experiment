import YangMills.Construction.InfiniteLattice.HyperoctahedralMotionsAndCubes
import YangMills.Construction.Torus.SeparatedTuplesAndIsometriesOfTorusOrFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open TestFunctions
open ReflectionPositivity.AxisMirror (Ambient)
open scoped ENNReal
noncomputable section
namespace AmbientPoints
variable {s : Conventions.StandingParameters} {E : Ambient} {n : ℕ}
def lipSeparatedTuples (s : Conventions.StandingParameters) (E : Ambient) (n : ℕ) :
    Set (Fin n → Pt s E → ℝ) :=
  {f | (∀ i, IsLipschitzFor (pointDist s E) (f i) ∧ IsCompact (tsupport (f i))) ∧
    Pairwise fun i j => Disjoint (tsupport (f i)) (tsupport (f j))}
def allLipSeparatedTuples (s : Conventions.StandingParameters) (E : Ambient) :
    Set (FunctionTuple s E) :=
  {X | X.2 ∈ lipSeparatedTuples s E X.1}
def separatedTuplesSmoothOrLip (s : Conventions.StandingParameters) (E : Ambient) :
    Set (FunctionTuple s E) :=
  allSeparatedTuples s E ∪ allLipSeparatedTuples s E
def supportSeparation {V : Type*} [Zero V] (f : Fin n → Pt s E → V) : ℝ≥0∞ :=
  ⨅ i, ⨅ k, ⨅ _ : i ≠ k, setDist s E (tsupport (f i)) (tsupport (f k))
def IsClosedBallRadius (s : Conventions.StandingParameters) (E : Ambient) (R : ℝ)
    (A : Set (Pt s E)) : Prop :=
  0 < R ∧ ∃ x, A = closedBall s E x R
def IsSupportedInBalls {V : Type*} [Zero V] (R : ℝ) (f : Fin n → Pt s E → V) : Prop :=
  ∀ i, ∃ B, IsClosedBallRadius s E R B ∧ tsupport (f i) ⊆ B
def restrictSigmaTuple {A : Type*} (X : Σ k : ℕ, Fin k → A) (J : Finset (Fin X.1)) :
    Σ k : ℕ, Fin k → A :=
  ⟨J.card, restrictTuple X.2 J⟩
def tupleAppend {A : Type*} (X Y : Σ k : ℕ, Fin k → A) : Σ k : ℕ, Fin k → A :=
  ⟨X.1 + Y.1, Fin.append X.2 Y.2⟩
theorem nilTuple_tupleAppend (Y : FunctionTuple s E) :
    tupleAppend (nilTuple s E) Y = Y := by
  obtain ⟨k, h⟩ := Y
  refine Sigma.ext (Nat.zero_add k) ?_
  refine (Fin.heq_fun_iff (Nat.zero_add k)).2 fun i => ?_
  have key : ∀ (a : Fin 0 → Pt s E → ℝ) (j : Fin (0 + k)),
      Fin.append a h j = h (Fin.cast (Nat.zero_add k) j) := fun a j => by
    rw [Fin.append_left_nil _ _ rfl]
    rfl
  exact key (nilTuple s E).2 i
theorem tupleAppend_nilTuple (X : FunctionTuple s E) :
    tupleAppend X (nilTuple s E) = X := by
  obtain ⟨k, f⟩ := X
  refine congrArg (Sigma.mk k) ?_
  funext i
  exact Fin.append_left f _ i
def mapComponents {A B : Type*} (φ : A → B) (X : Σ k : ℕ, Fin k → A) : Σ k : ℕ, Fin k → B :=
  ⟨X.1, fun i => φ (X.2 i)⟩
def translateEquiv (s : Conventions.StandingParameters) (v : Fin 4 → ℝ) :
    Pt s .euclidean ≃ Pt s .euclidean :=
  (Equiv.addRight v : (Fin 4 → ℝ) ≃ (Fin 4 → ℝ))
def translateFn {V : Type*} (v : Fin 4 → ℝ) (f : Pt s .euclidean → V) :
    Pt s .euclidean → V :=
  fun x : Fin 4 → ℝ => f (x - v)
theorem translateFn_eq_transportFn {V : Type*} (v : Fin 4 → ℝ)
    (f : Pt s .euclidean → V) :
    translateFn v f = transportFn (translateEquiv s v) f := by
  have key : ∀ a : Fin 4 → ℝ, a - v = (Equiv.addRight v).symm a := fun a => by
    simp [sub_eq_add_neg]
  funext x
  exact congrArg f (key x)
def translateTuple {V : Type*} (v : Fin 4 → ℝ) (X : Σ k : ℕ, Fin k → Pt s .euclidean → V) :
    Σ k : ℕ, Fin k → Pt s .euclidean → V :=
  mapComponents (translateFn v) X
def signedPermFn {V : Type*} (w : InfiniteLattice.hyperoctahedralLinearGroup)
    (f : Pt s .euclidean → V) : Pt s .euclidean → V :=
  fun x : Fin 4 → ℝ =>
    f ((w : InfiniteLattice.AmbientSpace ≃ₗ[ℝ] InfiniteLattice.AmbientSpace).symm x)
def signedPermTuple {V : Type*} (w : InfiniteLattice.hyperoctahedralLinearGroup)
    (X : Σ k : ℕ, Fin k → Pt s .euclidean → V) : Σ k : ℕ, Fin k → Pt s .euclidean → V :=
  mapComponents (signedPermFn w) X
def FitsInTorusHalfSide {V : Type*} [Zero V] (t : Conventions.StandingParameters)
    (f : Fin n → Pt s .euclidean → V) : Prop :=
  ∃ A : Set (Pt s .euclidean), setDiam s .euclidean A ≤ ENNReal.ofReal (t.side / 2) ∧
    ∀ i, tsupport (f i) ⊆ A
def periodizedTuple {V : Type*} [AddCommMonoid V] [TopologicalSpace V]
    (t : Conventions.StandingParameters) (f : Fin n → Pt s .euclidean → V) :
    Fin n → Pt t .torus → V :=
  fun i => periodize (PeriodicLattice.torusSide t.L t.m) (f i)
end AmbientPoints
end
end YangMills.Construction
