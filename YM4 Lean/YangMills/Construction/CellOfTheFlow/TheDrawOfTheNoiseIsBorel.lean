import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
open TorusFields TorusLumps StepSettings RenormalizationStepParameters WeightedResponses ResponseInTheExpansion BlockAverages LumpContours
def sampleChainMeasurableStatement : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (S : ChainSampler T), T.MarksMeasurable →
    (∀ s, (S s).IsFaithful) →
    ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
      Measurable fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => sampleChain T S s n p.1 p.2
end YangMills.Construction.CellWindows
end
