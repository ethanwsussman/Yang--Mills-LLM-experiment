import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.FramesOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.PartsOfAHullExpansion
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open BlockAverages TorusLumps StepSettings
def CoarseStatesFormHullExpansion : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → R.ColdChainFits → ∀ h : CoarseLabelFacts R,
    HullExpansionStates R.params R.nextCoupling (kernelImage R.params R.coupling R.functional)
      (coarseLabelSpace R h) (coarseWeightExpansion R) (coarseFactorExpansion R)
end YangMills.Construction.ClusterExpansionOfAStep
end
