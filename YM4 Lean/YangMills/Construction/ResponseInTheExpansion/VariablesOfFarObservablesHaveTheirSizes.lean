import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.FunctionsOfTheCases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open WeightedResponses TorusFields StepSettings StepGas FreeEnergies TorusLumps StepCosts
def centeredSupportResponseBounds : Prop :=
  HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (V : TorusField n) (f : PlaquetteWeight (fineSide R.params.side (R.depth + 1) n)),
    weightNorm R.params.side R.depth f ≤ 1 → (upperSites f).Nonempty →
    (∀ (Yt : Finset (TorusSite (n * R.params.side))) (bad : Finset (TorusBond (n * R.params.side)))
        (b : BaseChoice R.params.side n),
      Measurable fun p : TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        liveCaseFunction (centeredSupportResponse A V f) p.1 Yt p.2 bad b) ∧
    IsGaugeInvariantCase (liveCaseFunction (centeredSupportResponse A V f)) ∧
    ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusBond (n * R.params.side))) (b : BaseChoice R.params.side n),
      IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |centeredSupportResponse A V f W Yt ωt bad b| ≤
        4 * lowerSizeConst A f * meanSiteScore A.score (lowerSites f) Yt ωt
end YangMills.Construction.ResponseInTheExpansion
end
