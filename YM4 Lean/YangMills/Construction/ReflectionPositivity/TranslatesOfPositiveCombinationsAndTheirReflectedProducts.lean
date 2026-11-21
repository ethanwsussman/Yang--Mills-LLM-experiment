import YangMills.Construction.ReflectionPositivity.FormOfAFunctionalOnSeparatedTuples
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction.SeparatedTuples
open InfiniteLattice (AmbientSpace)
open ReflectionPositivity.TupleForm (PositiveSpan reflectConj)
namespace PositiveTranslates
def Statement : Prop :=
  ∀ (F F' : PositiveSpan) (v : AmbientSpace), 0 ≤ v TimeAxis.timeIdx →
    pushSpan (translate v) F'.1 ∈ spanIn TimeAxis.upperHalfSpace ∧
    (∀ Z ∈ (reflectConj F).support, ∀ Y ∈ F'.1.support, SepTuple.Composable Z Y) ∧
    ∀ Z ∈ (reflectConj F).support, ∀ Y ∈ (pushSpan (translate v) F'.1).support,
      SepTuple.Composable Z Y
end PositiveTranslates
end YangMills.Construction.SeparatedTuples
