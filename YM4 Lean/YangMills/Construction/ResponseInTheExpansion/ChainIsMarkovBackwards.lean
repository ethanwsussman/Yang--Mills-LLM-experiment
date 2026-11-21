import YangMills.Construction.ResponseInTheExpansion.LocalSizesOfTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.ResponseInTheExpansion
open YangMills.Construction.WeightedResponses
open Classical
open MeasureTheory
def chainMarkovBackwardsStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (t d n : ℕ) [NeZero n] (G : MarkedSample ℓ t (fineSide ℓ.side d n) → ℝ) (B : ℝ), Measurable G → (∀ v, |G v| ≤ B) →
      (markedSampleLaw T β (t + d) n)[fun u => G (sampleBelow ℓ t d n u) | upperSigma T t d n] =ᵐ[markedSampleLaw T β (t + d) n]
        (markedSampleLaw T β (t + d) n)[fun u => G (sampleBelow ℓ t d n u) |
          (stageSigma T t (fineSide ℓ.side d n)).comap (sampleBelow ℓ t d n)]
end YangMills.Construction.ResponseInTheExpansion
end
