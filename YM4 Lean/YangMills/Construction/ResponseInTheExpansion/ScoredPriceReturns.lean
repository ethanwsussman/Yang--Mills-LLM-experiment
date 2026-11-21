import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open StepSettings WeightedResponses ClusterExpansionOfAStep
def ScoredPriceCoversCoarseScore : Prop :=
  HoldsAtEveryStep fun T R A => R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    ∀ hL : CoarseLabelFacts R,
      PriceBoundsScore R.params R.nextCoupling (coarseLabelSpace R hL) (coarseFactorExpansion R)
        (R.stateDensity T.lam) (coarseLabelScore A.responseParams.s₁ A.score)
end YangMills.Construction.ResponseInTheExpansion
end
