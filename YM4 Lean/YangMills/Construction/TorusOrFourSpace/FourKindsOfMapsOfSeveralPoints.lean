import YangMills.Construction.TorusOrFourSpace.IsometriesLargestDistanceAndOrdersOnOpenSubsets
import YangMills.Construction.TorusOrFourSpace.PermutationsDiagonalActionsTranslationsAndInvariance
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.Kind
variable (D : Params) (E : Kind)
def isometryInverse (σ : E.Pt D → E.Pt D) : E.Pt D → E.Pt D :=
  haveI : Nonempty (E.Pt D) := ⟨E.quotMap D 0⟩
  Function.invFun σ
inductive ExtendedTupleMap (D : Params) (E : Kind) (n : ℕ+) where
  | ofTupleMap (ψ : TupleMap D E n)
  | ofIsometry (σ : E.Pt D → E.Pt D) (hσ : IsIsometry D E σ)
variable {D E} {n : ℕ+}
def compEach {Z : Type*} {k : ℕ} (f : Fin k → E.Pt D → Z) (σ : E.Pt D → E.Pt D) :
    Fin k → E.Pt D → Z :=
  fun i => f i ∘ σ
def InvariantUnder (ψ : E.Tuple D n → E.Tuple D n)
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ) : Prop :=
  ∀ (F : Tuple.testFns D E (pairwiseDistinct D E n))
    (h : F.1 ∘ ψ ∈ Tuple.testFns D E (pairwiseDistinct D E n)),
    T ⟨_, h⟩ = T F
namespace ExtendedTupleMap
def actPts : ExtendedTupleMap D E n → E.Tuple D n → E.Tuple D n
  | ofTupleMap ψ, y => ψ.actPts y
  | ofIsometry σ _, y => fun i => σ (y i)
def actFns {Z : Type*} :
    ExtendedTupleMap D E n → (Fin (n : ℕ) → E.Pt D → Z) → Fin (n : ℕ) → E.Pt D → Z
  | ofTupleMap ψ, f => ψ.actFns f
  | ofIsometry σ _, f => compEach f (isometryInverse D E σ)
def InvariantFunctional {Z : Type*} (ψ : ExtendedTupleMap D E n)
    (Φ : sepC1Tuples D E (n : ℕ) → Z) : Prop :=
  ∀ (f : sepC1Tuples D E (n : ℕ)) (h : ψ.actFns f.1 ∈ sepC1Tuples D E (n : ℕ)),
    Φ ⟨_, h⟩ = Φ f
def InvariantDistrib (ψ : ExtendedTupleMap D E n)
    (T : Tuple.testFns D E (pairwiseDistinct D E n) → ℂ) : Prop :=
  InvariantUnder ψ.actPts T
end ExtendedTupleMap
end YangMills.Construction.PeriodicSpace.Kind
end
