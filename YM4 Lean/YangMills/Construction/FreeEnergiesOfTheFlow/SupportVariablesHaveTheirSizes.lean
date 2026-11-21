import YangMills.Construction.FreeEnergiesOfTheFlow.SupportsOverAStepDefs
import YangMills.Construction.ResponseInTheExpansion.FunctionsOfTheCases
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergies
def supportResponseBoundStatement : Prop :=
  WeightedResponses.HoldsAtEveryStep fun _ R A => ∀ (n : ℕ) [NeZero n], R.params.n₀ ≤ n →
    ∀ (V : TorusFields.TorusField n) (f : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide R.params.side (R.depth + 1) n)),
    WeightedResponses.weightNorm R.params.side (R.depth + 1) f ≤ 1 → WeightedResponses.weightNorm R.params.side R.depth f ≤ 1 →
    (upperSites f).Nonempty →
    (∀ (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n),
      Measurable fun p : TorusFields.TorusField (n * R.params.side) × (Yt → R.labels.Ω) =>
        liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse A V f) p.1 Yt p.2 bad b) ∧
    WeightedResponses.IsGaugeInvariantCase (liveCaseFunction (ResponseInTheExpansion.centeredSupportResponse A V f)) ∧
    ∀ (W : TorusFields.TorusField (n * R.params.side)) (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusFields.TorusBond (n * R.params.side))) (b : StepCosts.BaseChoice R.params.side n),
      WeightedResponses.IsLiveState R.params R.coupling R.labelWeight W Yt ωt →
      |ResponseInTheExpansion.centeredSupportResponse A V f W Yt ωt bad b| ≤
        4 * lowerSizeConst A f * ResponseInTheExpansion.meanSiteScore A.score (lowerSites f) Yt ωt
end YangMills.Construction.FreeEnergies
end
