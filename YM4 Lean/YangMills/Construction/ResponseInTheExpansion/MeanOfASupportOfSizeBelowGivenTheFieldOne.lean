import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields StepSettings StepGas FreeEnergies TorusLumps
def supportResponseMeanBound : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n),
    weightNorm R.params.side R.depth f ≤ 1 → (upperSites f).Nonempty →
    |caseMean R ∅ (trivialField n) (emptyCoarseState R) (supportResponseSum A (trivialField n) f)| ≤
      (A.responseParams.C₀ + 1 + 16 * R.params.coupling) * ((lowerSites f).card : ℝ)
end YangMills.Construction.ResponseInTheExpansion
end
