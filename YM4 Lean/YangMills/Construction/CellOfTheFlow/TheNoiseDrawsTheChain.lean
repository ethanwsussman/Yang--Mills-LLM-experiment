import YangMills.Construction.CellOfTheFlow.NoiseOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.CellWindows
def sampleChainLawStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → ∀ (T : WeightedResponses.StageTower ℓ) (S : ChainSampler T)
    (β : ℝ), 0 < β →
    ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable → (∀ s, (S s).IsFaithful) →
    ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
      Measurable (fun p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side s n) × ChainNoise ℓ s n =>
        sampleChain T S s n p.1 p.2) ∧
      Measure.map (fun p : TorusFields.TorusField (WeightedResponses.fineSide ℓ.side s n) × ChainNoise ℓ s n =>
        sampleChain T S s n p.1 p.2)
        ((WeightedResponses.wilsonLaw β (WeightedResponses.fineSide ℓ.side s n)).prod (chainNoiseMeasure ℓ s n)) =
        WeightedResponses.markedSampleLaw T β s n
end YangMills.Construction.CellWindows
end
