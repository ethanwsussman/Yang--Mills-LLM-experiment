import YangMills.Construction.ResponseInTheExpansion.ResponsesOfTheExpansion
import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusLumps ColdStepAtMirrorFrames WeightedResponses
def ResponseIsConditionalExpectation : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      response T β al s n h =ᵐ[markedSampleLaw T β s n]
        (markedSampleLaw T β s n)[fun u =>
          chainMark ℓ (fun j => (T.stage j).coupling) al s n h (forgetMarks ℓ s n u) |
          stageSigma T s n]
end ResponseInTheExpansion
end YangMills.Construction
end
