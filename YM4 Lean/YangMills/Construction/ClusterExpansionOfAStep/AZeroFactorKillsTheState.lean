import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace ClusterExpansionOfAStep
open TorusLumps TorusFields StepSettings
def CoarseWeightZeroOfFactorZero : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
      (∃ X ∈ chainComponents R.nextRange q.1, coarseFactor V q X = 0) →
        coarseStateWeight R (hotCoreSites R V) V q = 0
end ClusterExpansionOfAStep
end YangMills.Construction
end
