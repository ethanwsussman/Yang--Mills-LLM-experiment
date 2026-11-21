import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.BoxMarks
open WeightedResponses ResponseInTheExpansion
def lowerMarginalStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side →
    ∀ T : StageTower ℓ, ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn →
      T.MarksMeasurable → ∀ (β : ℝ) (k s N : ℕ) [NeZero N],
        Measure.map (sampleBelow ℓ k s N) (markedSampleLaw T β (k + s) N) =
          markedSampleLaw T β k (fineSide ℓ.side s N)
end YangMills.Construction.BoxMarks
end
