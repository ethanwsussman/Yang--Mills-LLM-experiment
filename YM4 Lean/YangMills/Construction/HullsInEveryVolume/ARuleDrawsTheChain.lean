import YangMills.Construction.HullsInEveryVolume.NoisesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction.ChainNoise
open TorusLumps TorusFields WeightedResponses
def ruleDrawsChainStatement : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → ∀ (T : StageTower ℓ) (rule : NoiseRule ℓ) (β : ℝ),
    ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable → rule.IsAdmissible T →
    ∀ (s n : ℕ) [NeZero n], ℓ.side ∣ n → 64 ≤ n →
      Measurable (fun p : TorusField (fineSide ℓ.side s n) × ChainNoise ℓ s n => rule.chain T s n p.1 p.2) ∧
      ((wilsonLaw β (fineSide ℓ.side s n)).prod (chainNoiseLaw ℓ s n)).map (fun p => rule.chain T s n p.1 p.2) =
        markedSampleLaw T β s n
end YangMills.Construction.ChainNoise
end
