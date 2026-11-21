import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxLaws
open TorusLumps TorusFields StepSettings StepCosts WeightedResponses ColdStepAtMirrorFrames
def BondFitTailBound : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (params : StepParameters), 1 ≤ params.coupling → ∀ (T : StageTower params) (β : ℝ),
    IsCutoff (params.threshold / 64) T.base.barrierFn →
    T.MarksMeasurable → ∀ (j n : ℕ) [NeZero n],
      IsProbabilityMeasure (markedSampleLaw T β j (n * params.side)) →
      0 ≤ (T.stage j).coupling → ∀ (b : TorusBond n) (t : ℝ),
        (markedSampleLaw T β (j + 1) n).real
            {u | t < bondFit params (topField params j (n * params.side) u.1) u.2.2.1 u.2.1 b} ≤
          Real.exp (C * Real.log (2 + params.coupling * (T.stage j).coupling) -
            params.coupling * (T.stage j).coupling * t)
end YangMills.Construction.BoxLaws
end
