import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.HullsInEveryVolume
open TorusFields WeightedResponses ChainNoise
def noiseChainMeasurableStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (rule : NoiseRule ℓ),
    T.MarksMeasurable → rule.IsAdmissible T →
    ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
      Measurable fun p : TorusField (fineSide ℓ.side s n) × ChainNoise.ChainNoise ℓ s n => rule.chain T s n p.1 p.2
end YangMills.Construction.HullsInEveryVolume
end
