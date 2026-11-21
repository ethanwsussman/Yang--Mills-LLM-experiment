import YangMills.Construction.ClusterExpansionOfAStep.MarksOfAStep
import YangMills.Construction.ClusterExpansionOfAStep.ParametersOfARenormalizationStep
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.HullsInEveryVolume
open Classical in
def badBlocksPaidByEnergy : Prop :=
  ∀ (Tb : RenormalizationStepParameters.ParameterAssignment) (y : ℝ), Tb.Admissible → (Tb.stepParameters y).Admissible →
    ∀ c : WeightedResponses.ChainStage (Tb.stepParameters y),
    c.anchorRadius = Tb.ρA → ColdStepAtMirrorFrames.IsCutoff ((Tb.stepParameters y).threshold / 64) c.barrierFn →
    StepMarks.RangesAdmissible (TorusLumps.clusterRange c.coupling) (TorusLumps.clusterRange c.nextCoupling) →
    Tb.N 0 * Tb.threshold * Real.exp (-(Tb.δ₁ * ((TorusLumps.clusterRange c.coupling / 2 ^ 11 : ℕ) : ℝ))) ≤
      Tb.threshold / 512 →
    ∀ (n : ℕ) [NeZero n], TorusLumps.IsBlockTorusSide (Tb.stepParameters y) n →
      ∀ (V : TorusFields.TorusField n) (W : TorusFields.TorusField (n * (Tb.stepParameters y).side))
        (b : StepCosts.BaseChoice (Tb.stepParameters y).side n)
        (bad : Finset (TorusFields.TorusBond (n * (Tb.stepParameters y).side))),
        b ∈ TorusLumps.baseChoices (Tb.stepParameters y)
          (TorusFields.readAtLevel (TorusLumps.stepBlockFrame (Tb.stepParameters y).side n) 0 W) →
        WeightedResponses.markLaw c.toStepSetup W V bad ≠ 0 →
        Tb.cE * ((bad.image fun e => TorusLumps.parentBlock (Tb.stepParameters y).side e.1).card : ℝ) ≤
          TorusFields.actionAtLevel Tb.coupling Tb.side c.depth
              (Finset.univ \ TorusLumps.thickening LumpContours.lumpRange
                (TorusLumps.torusHotSites (Tb.stepParameters y) W)) W +
            Tb.κ * Tb.threshold ^ 2 * ((TorusLumps.torusHotLumps (Tb.stepParameters y) W).card : ℝ) +
            Tb.coupling * ∑ e : TorusFields.TorusBond n, StepCosts.bondFit (Tb.stepParameters y) W V b e
end YangMills.Construction.HullsInEveryVolume
end
