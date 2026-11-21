import YangMills.Construction.Continuum.FormsOfTheSeparatedTuplesOfFourSpaceTheirSpanAndFunctionals
import YangMills.Construction.Continuum.SubTuplesIsometriesAndTheConjugateOnFourSpace
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.BoundsOnEverySide
def IsRecenteredLimitFunctional {s : Conventions.StandingParameters}
    (σ σS : R4TupleForms.FinTuple s → ℝ) : Prop :=
  ∀ X : R4TupleForms.FinTuple s, σS X = ∑ I : Finset (Fin (Continuum.SeparatedFourTuples.tupleLength X)),
    σ (Continuum.SeparatedFourTuples.sepSubTuple X I) *
      ∏ i ∈ Iᶜ, (-σ (Continuum.SeparatedFourTuples.sepSubTuple X {i}))
end YangMills.Construction.BoundsOnEverySide
end
