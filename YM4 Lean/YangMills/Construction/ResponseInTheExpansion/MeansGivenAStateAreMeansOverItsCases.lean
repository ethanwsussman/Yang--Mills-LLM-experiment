import YangMills.Construction.ResponseInTheExpansion.PairsAtALevel
import YangMills.Construction.ResponseInTheExpansion.ResponseOfAStep
import YangMills.Construction.ResponseInTheExpansion.TowerAtTheParameters
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ResponseInTheExpansion
open BlockAverages LumpContours ColdStepAtMirrorFrames WeightedResponses StepSettings TorusLumps TorusFields
def conditionalMeanIsCaseMeanStatement : Prop :=
  HoldsAtAdmissibleParameters fun Tb y => ∀ (T : StageTower (Tb.stepParameters y)) (β : ℝ) (s n : ℕ) [NeZero n],
    IsTowerAtParameters Tb y T β s → IsCutoff ((Tb.stepParameters y).threshold / 64) T.base.barrierFn →
    T.MarksMeasurable →
    (T.stage s).toStepSetup.IsWellPosed →
    IsBlockTorusSide (Tb.stepParameters y) (n * (Tb.stepParameters y).side) → (Tb.stepParameters y).side ∣ n →
    ∀ F : TorusField n → CaseFunction (T.stage s).toStepSetup n,
      (Measurable fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
        F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1) →
      (∃ C : ℝ, ∀ u : MarkedSample (Tb.stepParameters y) (s + 1) n,
        |F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
          (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1| ≤ C) →
      ((markedSampleLaw T β (s + 1) n)[fun u : MarkedSample (Tb.stepParameters y) (s + 1) n =>
          F u.2.2.1 (topField (Tb.stepParameters y) s (n * (Tb.stepParameters y).side) u.1)
            (stageState T s (n * (Tb.stepParameters y).side) u.1).2.1
            (stageState T s (n * (Tb.stepParameters y).side) u.1).2.2 u.2.2.2 u.2.1 |
          stageSigma T (s + 1) n]) =ᵐ[markedSampleLaw T β (s + 1) n]
        fun u => caseMean (T.stage s).toStepSetup (hotCoreSites (T.stage s).toStepSetup u.2.2.1) u.2.2.1
          (stageState T (s + 1) n u).2 (F u.2.2.1)
end YangMills.Construction.ResponseInTheExpansion
end
