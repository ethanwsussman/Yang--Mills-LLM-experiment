import YangMills.Construction.ClusterExpansionOfAStep.DensitiesOfTheImageForm
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace WeightedResponses
open TorusLumps StepSettings ClusterExpansionOfAStep
def StepHasResponseBounds (R : StepSetup) (A : ResponseSetup R) (hL : CoarseLabelFacts R) (c : ℝ) : Prop :=
  ∃ Ra Rb : LocalDensity,
    ResponseBounds R.params A.responseParams (R.depth + 1) R.nextCoupling c (coarseLabelSpace R hL)
      (coarseWeightExpansion R) (coarseLabelScore A.responseParams.s₁ A.score) A.coldStep A.hullStep Ra Rb
def StepIsScored (lam : ℝ) (R : StepSetup) (A : ResponseSetup R) (hL : CoarseLabelFacts R) : Prop :=
  ColdExpansion R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
      (R.renormalizedDensity lam) ∧
  HullExpansion R.params (R.depth + 1) R.nextCoupling (kernelImage R.params R.coupling R.functional)
    (R.renormalizedDensity lam) (coarseLabelSpace R hL) (coarseWeightExpansion R)
    (coarseFactorExpansion R) (R.stateDensity lam) ∧
  PriceBoundsScore R.params R.nextCoupling (coarseLabelSpace R hL) (coarseFactorExpansion R) (R.stateDensity lam)
    (coarseLabelScore A.responseParams.s₁ A.score)
end WeightedResponses
end YangMills.Construction
end
