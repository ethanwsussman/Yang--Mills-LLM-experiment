import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import YangMills.Construction.ResponseInTheExpansion.ConditionsOfAResponse
import YangMills.Construction.ResponseInTheExpansion.ResponseInASetting
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.StepSettings YangMills.Construction.WeightedResponses YangMills.Construction.ClusterExpansionOfAStep YangMills.Construction.TorusLumps
def hotRegimeStepStatement : Prop :=
  HoldsAtEveryStep fun T R A => R.IsWellPosed → R.nextCoupling = R.shiftedCoupling T.lam →
    ∀ hL : CoarseLabelFacts R,
      PriceBoundsScore R.params R.nextCoupling (coarseLabelSpace R hL) (coarseFactorExpansion R)
        (R.stateDensity T.lam) (coarseLabelScore A.responseParams.s₁ A.score) ∧
      StepShapeBounds A hL ∧ StepDecayBounds A hL ∧ (coldStepSizeBound A → StepSizeBounds A hL)
end YangMills.Construction.ResponseInTheExpansion
end
