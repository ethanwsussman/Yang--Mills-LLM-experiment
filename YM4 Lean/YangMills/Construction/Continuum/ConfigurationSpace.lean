import Mathlib
open scoped ContDiff ENNReal
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ConfigurationSpace
abbrev Config (n : ℕ) : Type := Fin n → Fin 4 → ℝ
abbrev CoordIndex (n : ℕ) : Type := Fin n ×ₗ Fin 4
def coords {n : ℕ} (x : Config n) : CoordIndex n → ℝ :=
  fun j => x (ofLex j).1 (ofLex j).2
theorem coords_toLex {n : ℕ} (x : Config n) (i : Fin n) (c : Fin 4) :
    coords x (toLex (i, c)) = x i c := rfl
def boxProduct {n : ℕ} (S : Fin n → Set (Fin 4 → ℝ)) : Set (Config n) :=
  {x | ∀ i, x i ∈ S i}
section Norms
variable {I : Type*} [Fintype I]
def l2Norm (x : I → ℝ) : ℝ := Real.sqrt (∑ j, x j ^ 2)
def maxNorm (x : I → ℝ) : ℝ := ⨆ j, |x j|
end Norms
def configNorm {n : ℕ} (x : Config n) : ℝ := l2Norm (coords x)
def configMaxNorm {n : ℕ} (x : Config n) : ℝ := maxNorm (coords x)
abbrev MultiIdx (I : Type*) : Type _ := I → ℕ
section MultiIndices
variable {I : Type*} [Fintype I]
def MultiIdx.order (α : MultiIdx I) : ℕ := ∑ j, α j
def MultiIdx.choose (α β : MultiIdx I) : ℕ := ∏ j, (α j).choose (β j)
end MultiIndices
section Functions
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
def smoothSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] : Set (V → ℂ) :=
  {f | ContDiff ℝ ∞ f}
def testFunctionSet (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] :
    Set (V → ℂ) :=
  {f | f ∈ smoothSet V ∧ HasCompactSupport f}
def ofRealFun {X : Type*} (f : X → ℝ) : X → ℂ := fun x => (f x : ℂ)
def dirDeriv (v : V) (f : V → ℂ) : V → ℂ := fun x => lineDeriv ℝ f x v
def iterDirDeriv {I : Type*} [Fintype I] [LinearOrder I] (e : I → V) (α : MultiIdx I)
    (f : V → ℂ) : V → ℂ :=
  ((Finset.univ : Finset I).sort (· ≤ ·)).foldr
    (fun j g => (dirDeriv (e j))^[α j] g) f
end Functions
section PartialDerivatives
variable {I : Type*} [Fintype I] [LinearOrder I]
def multiDeriv (α : MultiIdx I) (f : (I → ℝ) → ℂ) : (I → ℝ) → ℂ :=
  iterDirDeriv (fun j => Pi.single j 1) α f
end PartialDerivatives
def coordBasis {n : ℕ} (j : CoordIndex n) : Config n :=
  Pi.single (ofLex j).1 (Pi.single (ofLex j).2 1)
def configMultiDeriv {n : ℕ} (α : MultiIdx (CoordIndex n)) (f : Config n → ℂ) :
    Config n → ℂ :=
  iterDirDeriv coordBasis α f
def IsNonzeroSomewhere {X E : Type*} [Zero E] (f : X → E) : Prop :=
  {x | f x ≠ 0}.Nonempty
def IsConstEq {X E : Type*} (f : X → E) (a : E) : Prop :=
  ∀ x, f x = a
def pairDiagonal {n : ℕ} (i k : Fin n) : Set (Config n) := {x | x i = x k}
def orderedPairs (n : ℕ) : Finset (Fin n × Fin n) := Finset.univ.filter fun p => p.1 < p.2
def fatDiagonal (n : ℕ) : Set (Config n) :=
  ⋃ p ∈ orderedPairs n, pairDiagonal p.1 p.2
def minSeparation {n : ℕ} (x : Config n) : ℝ≥0∞ :=
  ⨅ p ∈ orderedPairs n, ENNReal.ofReal (maxNorm (x p.1 - x p.2))
theorem orderedPairs_one : orderedPairs 1 = ∅ := by
  decide
theorem prod_orderedPairs_one {M : Type*} [CommMonoid M] (f : Fin 1 × Fin 1 → M) :
    ∏ p ∈ orderedPairs 1, f p = 1 := by
  simp [orderedPairs_one]
theorem minSeparation_one : IsConstEq (minSeparation (n := 1)) ⊤ := by
  intro x
  simp [minSeparation, orderedPairs_one]
end YangMills.Construction.ConfigurationSpace
end
