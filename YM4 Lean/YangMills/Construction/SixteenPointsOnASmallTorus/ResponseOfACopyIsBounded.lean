import YangMills.Construction.SixteenPointsOnASmallTorus.LevelsOfACopyDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.SmallTorusCopies
def responseBoundedByScoreStatement : Prop :=
  ForAllLargeFloors fun T Kr y => ForAllInitialStages T y fun β hL z₀ => ∀ s : ℕ,
    ResponseInTheExpansion.StagesOnFlowUpTo T Kr y β hL z₀ s →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide (T.stepParameters y) n →
    ∀ f : ResponseInTheExpansion.StageWeight hL T.lam (ResponseInTheExpansion.couplingsAlongFlow (T.stepParameters y) β) z₀ s n,
      WeightedResponses.weightNorm (T.stepParameters y).side (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.depth f ≤ 1 →
      ∀ (W : TorusFields.TorusField n) (Y : Finset (TorusFields.TorusSite n))
        (ω : Y → (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.labels.Ω),
        WeightedResponses.IsLiveState (T.stepParameters y) (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.coupling
          (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.labelWeight W Y ω →
        |ResponseInTheExpansion.supportResponseTotal (ResponseInTheExpansion.flowStages T y β hL z₀ s).2 f W Y ω| ≤
          Kr.C₀ * ((ResponseInTheExpansion.weightSupportSites (T.stepParameters y).side
              (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.depth n f).card : ℝ) *
            ResponseInTheExpansion.meanSiteScore (ResponseInTheExpansion.flowStages T y β hL z₀ s).2.score
              (ResponseInTheExpansion.weightSupportSites (T.stepParameters y).side
                (ResponseInTheExpansion.flowStages T y β hL z₀ s).1.depth n f) Y ω
end YangMills.Construction.SmallTorusCopies
end
