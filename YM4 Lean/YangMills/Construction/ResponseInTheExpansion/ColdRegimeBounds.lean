import YangMills.Construction.ResponseInTheExpansion.BoundsOfTheSmoothMoves
import YangMills.Construction.ResponseInTheExpansion.FramesMoveWithTheTop
import YangMills.Construction.ResponseInTheExpansion.MeanOfABlockRemainderNearItsValue
import YangMills.Construction.ResponseInTheExpansion.MeanOfARemainder
import YangMills.Construction.ResponseInTheExpansion.MeanOfTheBlockRemainder
import YangMills.Construction.ResponseInTheExpansion.OneStepToSecondOrder
import YangMills.Construction.ResponseInTheExpansion.RestAtACurvature
import YangMills.Construction.ResponseInTheExpansion.RestFreezes
import YangMills.Construction.ResponseInTheExpansion.RestHasTwoDerivatives
import YangMills.Construction.ResponseInTheExpansion.ScoreAtTheFrame
import YangMills.Construction.ResponseInTheExpansion.SharesAtTheFrame
import YangMills.Construction.SummableBoundsOfTheFlow.MeanOfOneFamilyInTheLawOfAnother
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.WeightedResponses
structure ColdRegimeEstimatesAt (T : ColdStepAtMirrorFrames.StepParameters) : Prop where
  smoothIncrements : SmoothIncrementExpectationsAt T
  scoreRemainder : ScoreRemainderDecayAt T
  frameShares : weightedFrameSharesStatementAt T
  conditionalMean : BlockMeans.ConditionalMeanBoundsAt T.a T.chainParams.ρA T.κ T.decayRate T.η₃ T.σ T.E T.CE
    T.coupling T.L T.n₀ T.p
  meanRemainder : meanRemainderBound T
  blockRemainder : blockRemainderMeanBound T
  dilation : dilationIdentityAt T
  secondOrder : dilationRemainderSecondOrderBound T
  locality : dilationRemainderLocalityBound T
  atCurvature : dilationRemainderAtCurvatureBound T
  equivariance : ResponseInTheExpansion.FramesEquivariantAt T
  incrementBounds : ∃ C : ℝ, ResponseInTheExpansion.smoothIncrementBoundsAt T C
  secondOrderMoments : ResponseInTheExpansion.GaussianMomentApproxAt T
  nearValue : blockSumExpectationNearValueAt T
def coldRegimeEstimatesStatement : Prop :=
  ColdStepAtMirrorFrames.EventuallyInParameters ColdRegimeEstimatesAt
end YangMills.Construction.WeightedResponses
end
