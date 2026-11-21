import YangMills.Construction.Continuum.ConnectedFunctionsCentredFunctionalsOnTheSpanAndCumulantsOfAState
import YangMills.Construction.Continuum.RecentringOfATupleAndOfACombination
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.CentredTupleValue
open YangMills.Construction.TupleLists (ofList toList)
open YangMills.Construction.SetPartition (atLeastTwoPartitions)
open YangMills.Construction.TestSpaces (IsMultilinearSepFunctional SepTuple SepTupleOfCard c1CompactSupp
  centredPart centredPartFunctional cumulant sepTupleNil singletonSepTuple centredTuple centring sepRestrict)
open YangMills.Construction.SeparatedTuples (FormalSpan TupleFunctional)
def centredValueFormula : Prop :=
  ∀ (s : SepTuple → ℝ), IsMultilinearSepFunctional s →
    ∀ F : TupleFunctional, (∀ X, F X = s (ofList X)) →
      (∀ Z : FormalSpan,
        (centredPartFunctional s).spanExtension Z = F.spanExtension (centring s Z)) ∧
      (∀ (k : ℕ) (X : SepTupleOfCard k),
        F.spanExtension (centredTuple s (toList ⟨k, X⟩)) =
          ((∑ π ∈ atLeastTwoPartitions (Finset.univ : Finset (Fin k)),
            ∏ B ∈ π.parts, cumulant s (sepRestrict X B) : ℝ) : ℂ)) ∧
      centredPart s sepTupleNil = 1 ∧
      (∀ (f : (Fin 4 → ℝ) → ℝ) (hf : f ∈ c1CompactSupp (Set.univ : Set (Fin 4 → ℝ))),
        centredPart s ⟨1, singletonSepTuple f hf⟩ = 0) ∧
      IsMultilinearSepFunctional (centredPart s)
end YangMills.Construction.CentredTupleValue
end
