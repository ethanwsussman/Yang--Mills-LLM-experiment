import YangMills.Construction.Continuum.SeparatedTuplesTheirConcatenationAndCombinationsOnFourSpace
import Mathlib
set_option autoImplicit false
namespace YangMills.Construction
open AmbientPoints Continuum.SeparatedFourTuples
open TestFunctions (HasSeparatedSupportsR4)
namespace CompactSeparation
def CompactSetsSeparated : Prop :=
  ∀ s : Conventions.StandingParameters,
    (∀ A A' : Set (EuclideanFour s), IsCompact A → IsCompact A' → Disjoint A A' →
      0 < setDist s .euclidean A A') ∧
    ∀ X : SepTuple s, ∃ d : ℝ,
      HasSeparatedSupportsR4 (E := ℝ) (tupleComponents X) d ∧
        ∀ I : Finset (Fin (tupleLength X)),
          HasSeparatedSupportsR4 (E := ℝ) (restrictTuple (tupleComponents X) I) d
end CompactSeparation
end YangMills.Construction
