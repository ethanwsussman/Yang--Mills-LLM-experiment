import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open TorusFields TorusLumps StepSettings StepCosts
def AdmissionIsProduct : Prop :=
  ∀ R : StepSetup, R.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide R.params n →
    ∀ (V : TorusField n) (q : CoarseState R n), IsHullState R.params R.nextRange V q.1 →
    ∀ (W : TorusField (n * R.params.side)) (Yt : Finset (TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusBond (n * R.params.side)))
      (b : BaseChoice R.params.side n), bad ⊆ markedBonds R (hotCoreSites R V) →
      IsHullState R.params R.range W Yt →
      (coarseStateOf R (hotCoreSites R V) W Yt ωt bad b = q ↔
        (∀ X ∈ chainComponents R.nextRange q.1,
          (q.restrict X).IsAdmissibleCoarseState (hotNeighbourhoodOn R X V) X) ∧
          q.IsExtension (hotCoreSites R V) W Yt ωt bad b)
end YangMills.Construction.ClusterExpansionOfAStep
end
