import YangMills.Construction.LawByMomentsOfTheFlow.LevelsOfALocalChainDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open Classical
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def localChainSmallUnderFluctuationsAt : Prop :=
  ∃ x₀ : ℝ, ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N] (nn : ℝ)
    (o : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side
      (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
      (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N))),
    ResponseInTheExpansion.IsLocalChainAbove Tb y T β k N nn x₀ → (Tb.stepParameters y).side ∣ N →
    ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β
        (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N),
      ResponseInTheExpansion.IsLocalEvent T k (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
        (ResponseInTheExpansion.localBlockSide (Tb.stepParameters y) β k) N u o →
      coldAlongSteps T (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.localBlockSide (Tb.stepParameters y) β k) (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u
          (ResponseInTheExpansion.siteAbove (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N) o) ∧
      coldAlongSteps T k (ResponseInTheExpansion.localBlockSide (Tb.stepParameters y) β k) (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u) o ∧
      (deviationsBoundedAlong T (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (nn / ((Tb.stepParameters y).side : ℝ) ^ ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.localLogScale (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 3 : ℝ)))
          (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u
          (ResponseInTheExpansion.siteAbove (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N) o) →
        deviationsBoundedAlong T k nn (ResponseInTheExpansion.localLogScale (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 3 : ℝ)))
          (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u) o →
        ResponseInTheExpansion.IsGaugeSmallAlong T k nn (ResponseInTheExpansion.localLogScale (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ)))
          (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u) o
          (ResponseInTheExpansion.axialGaugeAt (Tb.stepParameters y)
            (WeightedResponses.topField (Tb.stepParameters y) (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
              (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
              (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u))
            (ResponseInTheExpansion.siteAbove (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
              (WeightedResponses.fineSide (Tb.stepParameters y).side (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N) o)))
def localChainSmallUnderFluctuationsStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies localChainSmallUnderFluctuationsAt
end YangMills.Construction.MomentLaw
end
