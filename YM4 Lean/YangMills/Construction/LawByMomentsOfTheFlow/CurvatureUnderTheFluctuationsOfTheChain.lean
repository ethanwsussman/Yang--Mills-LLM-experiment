import YangMills.Construction.LawByMomentsOfTheFlow.LevelsOfALocalChainDefs
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.MomentLaw
open Classical
variable (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ)
def curvatureBelowFluctuationMassAt : Prop :=
  ∃ C x₀ : ℝ, ∀ (T : WeightedResponses.StageTower (Tb.stepParameters y)) (β : ℝ) (k N : ℕ) [NeZero N]
    (o : TorusFields.TorusSite (WeightedResponses.fineSide (Tb.stepParameters y).side
      (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
      (WeightedResponses.fineSide (Tb.stepParameters y).side
        (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N))),
    ResponseInTheExpansion.IsLocalChainAbove Tb y T β k N 1 x₀ → (Tb.stepParameters y).side ∣ N →
    ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β
        (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k
          + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N),
      ResponseInTheExpansion.IsLocalEvent T k (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.localBlockSide (Tb.stepParameters y) β k) N u o →
      ResponseInTheExpansion.IsGaugeSmallAlong T k 1 (ResponseInTheExpansion.localLogScale (Tb.stepParameters y) β k)
          (ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 4 : ℝ)))
          (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
          (WeightedResponses.fineSide (Tb.stepParameters y).side
            (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
          (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y)
            (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
            (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u) o
          (ResponseInTheExpansion.axialGaugeAt (Tb.stepParameters y)
            (WeightedResponses.topField (Tb.stepParameters y)
              (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
              (WeightedResponses.fineSide (Tb.stepParameters y).side
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
              (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y)
                (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u))
            (ResponseInTheExpansion.siteAbove (Tb.stepParameters y).side
              (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
              (WeightedResponses.fineSide (Tb.stepParameters y).side
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N) o)) →
      ∀ μ ν : Fin 4, μ < ν →
        TorusFields.curvature (WeightedResponses.topField (Tb.stepParameters y) k _
            (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y) k
              (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) _
              (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y)
                (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u))) o μ ν ≤
          deviationMass T k 1 (ResponseInTheExpansion.localLogScale (Tb.stepParameters y) β k) Tb.ρA
              (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
              (WeightedResponses.fineSide (Tb.stepParameters y).side
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N)
              (ResponseInTheExpansion.sampleBelow (Tb.stepParameters y)
                (k + ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k)
                (ResponseInTheExpansion.localChainDepth (Tb.stepParameters y) β k) N u) o (o, μ, ν) +
            C * ResponseInTheExpansion.flowCouplings (Tb.stepParameters y) β k ^ (-(1 / 2 : ℝ))
def curvatureBelowFluctuationMassStatement : Prop :=
  ResponseInTheExpansion.HoldsOnParameterFamilies curvatureBelowFluctuationMassAt
end YangMills.Construction.MomentLaw
end
