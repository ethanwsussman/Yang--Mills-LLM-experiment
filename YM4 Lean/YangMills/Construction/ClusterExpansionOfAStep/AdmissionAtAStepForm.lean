import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction
namespace StepSettings
structure StepSetup.ReadsCaseTests (R : StepSetup) : Prop where
  hasExpansions : R.HasExpansions
  admissible : R.params.Admissible
  range_le : R.range ≤ R.nextRange + 1
  nextRange_ge : 2 ^ 16 ≤ R.nextRange
  range_ge_side : 2 ^ 40 * R.params.side ≤ R.range
end StepSettings
namespace ClusterExpansionOfAStep
def AdmissionIffComponentTests : Prop :=
  ∀ R : StepSettings.StepSetup, R.ReadsCaseTests → ∀ (n : ℕ) [NeZero n],
    TorusLumps.IsBlockTorusSide R.params n →
    ∀ (V : TorusFields.TorusField n) (q : StepSettings.CoarseState R n),
      TorusLumps.IsHullState R.params R.nextRange V q.1 →
    ∀ (W : TorusFields.TorusField (n * R.params.side))
      (Yt : Finset (TorusFields.TorusSite (n * R.params.side))) (ωt : Yt → R.labels.Ω)
      (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n),
      bad ⊆ StepSettings.markedBonds R (StepSettings.hotCoreSites R V) →
      TorusLumps.IsHullState R.params R.range W Yt →
      (StepSettings.coarseStateOf R (StepSettings.hotCoreSites R V) W Yt ωt bad b = q ↔
        (∀ X ∈ TorusLumps.chainComponents R.nextRange q.1,
            (q.restrict X).IsAdmissibleCoarseState (StepSettings.hotNeighbourhoodOn R X V) X) ∧
          q.IsExtension (StepSettings.hotCoreSites R V) W Yt ωt bad b)
end ClusterExpansionOfAStep
end YangMills.Construction
end
