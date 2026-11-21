import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.WeightedResponses
def forgetLastStepStatement : Prop :=
  ∀ (ℓ : YangMills.Construction.TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side →
    ∀ T : StageTower ℓ,
    YangMills.Construction.ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn →
    T.MarksMeasurable → ∀ (β : ℝ) (s n : ℕ) [NeZero n],
      IsProbabilityMeasure (markedSampleLaw T β s n) ∧
      MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
        (markedSampleLaw T β s (n * ℓ.side))
end YangMills.Construction.WeightedResponses
end
