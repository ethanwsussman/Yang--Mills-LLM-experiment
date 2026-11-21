import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.FreeEnergiesOfTheFlow
open TorusLumps WeightedResponses ColdStepAtMirrorFrames
def MarkedSampleTruncationPreserving : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (s n : ℕ) [NeZero n],
      MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
        (markedSampleLaw T β s (n * ℓ.side))
end YangMills.Construction.FreeEnergiesOfTheFlow
end
