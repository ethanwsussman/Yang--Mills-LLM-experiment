import YangMills.Construction.ClusterExpansionOfAStep.FactorsOfAStep
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ClusterExpansionOfAStep
open YangMills.Construction.StepSettings YangMills.Construction.TorusFields YangMills.Construction.TorusLumps YangMills.Construction.StepCosts YangMills.Construction.LumpContours
open Classical in
def ProdCoarseFactorEqStatement : Prop :=
  ∀ S : StepSetup, S.IsWellPosed → ∀ (n : ℕ) [NeZero n], IsBlockTorusSide S.params n →
    ∀ (V : TorusField n) (q : CoarseState S n) (W : TorusField (n * S.params.side))
      (Y : Finset (TorusSite (n * S.params.side)))
      (ω : Y → S.labels.Ω) (bad : Finset (TorusBond (n * S.params.side)))
      (b : BaseChoice S.params.side n),
      IsHullState S.params S.nextRange V q.1 → bad ⊆ markedBonds S (hotCoreSites S V) →
      IsHullState S.params S.range W Y →
      IsBaseChoice S.params.baseDepth (stepHotLumps S.params W) b →
      coarseStateOf S (hotCoreSites S V) W Y ω bad b = q →
      ∏ X ∈ chainComponents S.nextRange q.1, coarseFactor V q X =
        (∏ Z ∈ chainComponents S.range q.labelSet, S.clusterFactor (n * S.params.side) W Y ω Z) *
        (∏ c ∈ markedBonds S (hotCoreSites S V) ∩ bondsOverBlocks S.params.side q.markedZone,
          if c ∈ bad then 1 - bondMark S V W c else bondMark S V W c) *
        ∏ y ∈ q.markedZone, blockBaseWeight S.params (stepHotLumps S.params W)
          (torusSiteInFrame (stepBlockFrame S.params.side n) 1 y)
          (b (torusSiteInFrame (stepBlockFrame S.params.side n) 1 y))
end YangMills.Construction.ClusterExpansionOfAStep
end
