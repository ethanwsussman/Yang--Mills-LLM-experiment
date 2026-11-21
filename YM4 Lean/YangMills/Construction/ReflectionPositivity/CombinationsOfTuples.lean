import YangMills.Construction.ReflectionPositivity.SeparatedTuplesAndFunctionals
import Mathlib
set_option autoImplicit false
open scoped ComplexConjugate
noncomputable section
namespace YangMills.Construction.ReflectionPositivity.AxisMirror
namespace Ambient
variable (D : MirrorData) (E : Ambient)
abbrev TupleCombination (O : Set (E.Point D)) : Type := separatedWithin D E O →₀ ℂ
variable {D E} {O : Set (E.Point D)}
namespace TupleCombination
def basisVec (X : separatedWithin D E O) : TupleCombination D E O := Finsupp.single X 1
def sumOf {r : ℕ} (c : Fin r → ℂ) (X : Fin r → separatedWithin D E O) : TupleCombination D E O :=
  ∑ i, c i • basisVec (X i)
theorem exists_eq_sumOf (F : TupleCombination D E O) :
    ∃ (r : ℕ) (c : Fin r → ℂ) (X : Fin r → separatedWithin D E O), F = sumOf c X := by
  classical
  refine ⟨F.support.card, fun i => F (F.support.equivFin.symm i),
    fun i => F.support.equivFin.symm i, ?_⟩
  have hre : sumOf (fun i => F (F.support.equivFin.symm i)) (fun i => F.support.equivFin.symm i) =
      ∑ y : F.support, F y • basisVec (y : separatedWithin D E O) :=
    Fintype.sum_equiv F.support.equivFin.symm _ _ fun _ => rfl
  rw [hre, Finset.sum_coe_sort F.support fun y => F y • basisVec y]
  ext Y
  simp [basisVec, Finsupp.finsetSum_apply, Finsupp.single_apply]
end TupleCombination
def evalOrZeroC {A : Set (FnList D E)} (φ : A → ℂ) (X : FnList D E) : ℂ :=
  open Classical in if hX : X ∈ A then φ ⟨X, hX⟩ else 0
theorem evalOrZeroC_ofReal {A : Set (FnList D E)} (φ : A → ℝ) (X : FnList D E) :
    evalOrZeroC (fun Y => (φ Y : ℂ)) X = (evalOrZero φ X : ℂ) := by
  unfold evalOrZeroC evalOrZero
  split_ifs <;> simp
end Ambient
namespace CoordMirror
open Ambient
variable (D : MirrorData) (S : CoordMirror) (E : Ambient)
def reflectionForm (σ : separatedAll D E → ℂ)
    (F F' : TupleCombination D E (S.upperSide D E)) : ℂ :=
  F.sum fun X a => F'.sum fun Y b =>
    conj a * b * evalOrZeroC σ (S.reflectAppend D E X Y)
theorem reflectionForm_sumOf (σ : separatedAll D E → ℂ) {r r' : ℕ} (c : Fin r → ℂ)
    (X : Fin r → separatedWithin D E (S.upperSide D E)) (c' : Fin r' → ℂ)
    (Y : Fin r' → separatedWithin D E (S.upperSide D E)) :
    S.reflectionForm D E σ (TupleCombination.sumOf c X) (TupleCombination.sumOf c' Y) =
      ∑ i, ∑ k, conj (c i) * c' k *
        evalOrZeroC σ (S.reflectAppend D E (X i) (Y k)) := by
  have hsingle : ∀ (r : ℕ) (c : Fin r → ℂ)
      (X : Fin r → separatedWithin D E (S.upperSide D E)),
      TupleCombination.sumOf c X = ∑ i, Finsupp.single (X i) (c i) := fun r c X => by
    simp [TupleCombination.sumOf, TupleCombination.basisVec]
  rw [reflectionForm, hsingle r c X, hsingle r' c' Y, ← Finsupp.sum_finsetSum_index]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_single_index (by simp [Finsupp.sum]), ← Finsupp.sum_finsetSum_index]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [Finsupp.sum_single_index (by simp)]
    · intro y
      simp
    · intro y a b
      ring
  · intro x
    simp [Finsupp.sum]
  · intro x a b
    simp [Finsupp.sum, add_mul, Finset.sum_add_distrib]
end CoordMirror
end YangMills.Construction.ReflectionPositivity.AxisMirror
