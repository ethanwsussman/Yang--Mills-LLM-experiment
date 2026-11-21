import YangMills.Construction.ClusterExpansionOfAStep.AdmissionAtAStepForm
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open Classical in
def CaseFactorProductStatement : Prop :=
  ∀ R : StepSettings.StepSetup, R.ReadsCaseTests → ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide R.params n →
    ∀ (V : TorusFields.TorusField n) (q : StepSettings.CoarseState R n)
      (W : TorusFields.TorusField (n * R.params.side)) (Yt : Finset (TorusFields.TorusSite (n * R.params.side)))
      (ωt : Yt → R.labels.Ω) (bad : Finset (TorusFields.TorusBond (n * R.params.side)))
      (b : StepCosts.BaseChoice R.params.side n),
      TorusLumps.IsHullState R.params R.nextRange V q.1 →
      bad ⊆ StepSettings.markedBonds R (StepSettings.hotCoreSites R V) →
      TorusLumps.IsHullState R.params R.range W Yt →
      LumpContours.IsBaseChoice R.params.baseDepth (StepCosts.stepHotLumps R.params W) b →
      StepSettings.coarseStateOf R (StepSettings.hotCoreSites R V) W Yt ωt bad b = q →
      ∏ X ∈ TorusLumps.chainComponents R.nextRange q.1, StepSettings.coarseFactor V q X =
        (∏ Xc ∈ TorusLumps.chainComponents R.range q.labelSet, R.clusterFactor (n * R.params.side) W Yt ωt Xc) *
        (∏ c ∈ StepSettings.markedBonds R (StepSettings.hotCoreSites R V) ∩
            StepSettings.bondsOverBlocks R.params.side q.markedZone,
          if c ∈ bad then 1 - StepSettings.bondMark R V W c else StepSettings.bondMark R V W c) *
        ∏ y ∈ q.markedZone, StepSettings.blockBaseWeight R.params (StepCosts.stepHotLumps R.params W)
          (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 y)
          (b (StepCosts.torusSiteInFrame (TorusLumps.stepBlockFrame R.params.side n) 1 y))
end YangMills.Construction.ClusterExpansionOfAStep
end
