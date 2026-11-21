import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.TransfersOffTheWalk
open TorusFields StepGas WeightedResponses FreeEnergies
def supportResponseMeanAtTrivialFieldBound : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n → ∀ f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
    weightNorm R.params.side (R.depth + 1) f ≤ 1 → weightNorm R.params.side R.depth f ≤ 1 → (upperSites f).Nonempty →
    |caseMean R ∅ (trivialField n) (emptyCoarseState R) (ResponseInTheExpansion.supportResponseSum A (trivialField n) f)| ≤
      (A.responseParams.C₀ + 1 + 16 * R.params.coupling) * ((lowerSites f).card : ℝ)
end YangMills.Construction.TransfersOffTheWalk
end
