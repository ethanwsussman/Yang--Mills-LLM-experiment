import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.TupleProducts
open Kind
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (p : ℕ+),
    (∀ U : Fin (p : ℕ) → Set (E.Pt D),
      ((∀ i, Kind.IsOpenQ D E (U i)) →
        Tuple.IsOpenT D E (Tuple.boxSet D E U)) ∧
      ((∀ i, Kind.IsClosedQ D E (U i)) →
        Tuple.IsClosedT D E (Tuple.boxSet D E U)) ∧
      ((∀ i, Kind.IsCompactQ D E (U i)) →
        Tuple.IsCompactT D E (Tuple.boxSet D E U))) ∧
    (∀ i : Fin (p : ℕ),
      (∀ x x' : E.Tuple D p,
        Kind.quotDist D E (x i) (x' i) ≤ Tuple.tupleDist D E x x') ∧
      ∀ K : Set (E.Tuple D p), Tuple.IsCompactT D E K →
        Kind.IsCompactQ D E ((fun x : E.Tuple D p => x i) '' K)) ∧
    ∀ i i' : Fin (p : ℕ), i ≠ i' →
      Tuple.IsContinuousT D E
        (fun x : E.Tuple D p => Kind.quotDist D E (x i) (x i'))
end YangMills.Construction.PeriodicSpace.TupleProducts
