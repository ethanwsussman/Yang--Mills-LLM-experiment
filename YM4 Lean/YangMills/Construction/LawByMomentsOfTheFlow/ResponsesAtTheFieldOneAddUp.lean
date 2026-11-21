import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import YangMills.Construction.ResponseInTheExpansion.SeveralSupportsInOneStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
def responsesAtTrivialFieldSumStatement : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n),
    ∑ Y ∈ ResponseInTheExpansion.weightSupportSites R.params.side (R.depth + 1) n f,
        A.coldStep n Y (TorusFields.trivialField n) f =
      ∑ y ∈ ResponseInTheExpansion.weightSupportSites R.params.side R.depth (n * R.params.side) f,
          A.cold (n * R.params.side) y (TorusFields.trivialField (n * R.params.side)) f +
        WeightedResponses.caseMean R ∅ (TorusFields.trivialField n) (StepGas.emptyCoarseState R)
          (ResponseInTheExpansion.supportResponseSum A (TorusFields.trivialField n) f)
end YangMills.Construction.MomentLaw
end
