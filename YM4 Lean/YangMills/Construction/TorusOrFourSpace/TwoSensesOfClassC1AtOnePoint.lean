import YangMills.Construction.TorusOrFourSpace.CutOffsOnAProductOfOpenSets
import YangMills.Construction.TorusOrFourSpace.FunctionsOfClassC1SupportsAndNorms
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.PeriodicSpace.SingletonC1
open Kind
def Statement : Prop :=
  ∀ (D : Params) (E : Kind) (u : E.Pt D → ℝ),
    (Tuple.IsClassC D E 1 (Tuple.ofSingle D E fun x => (u x : ℂ)) ↔
      IsC1Fn D E u) ∧
    (IsC1Fn D E u →
      (∀ j : Fin 4,
        Tuple.partialDeriv D E
            (Pi.single (⟨j, by have := j.2; simp⟩ : Fin (4 * ((1 : ℕ+) : ℕ))) 1)
            (Tuple.ofSingle D E fun x => (u x : ℂ)) =
          Tuple.ofSingle D E fun x => (Kind.partialDeriv D E j u x : ℂ)) ∧
      Tuple.supportT D E (Tuple.ofSingle D E fun x => (u x : ℂ)) =
        Tuple.singleSet D E (Kind.supportQ D E u))
end YangMills.Construction.PeriodicSpace.SingletonC1
