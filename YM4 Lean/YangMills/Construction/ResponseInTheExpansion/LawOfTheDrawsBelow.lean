import YangMills.Construction.ResponseInTheExpansion.CurvatureOfALevelOnTheDraws
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory YangMills.Construction.ColdStepAtMirrorFrames
namespace YangMills.Construction
namespace ResponseInTheExpansion
open TorusLumps WeightedResponses
def sampleBelowLawStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable → ∀ (β : ℝ) (al : ℕ → ℝ),
      (∀ (s d n : ℕ) [NeZero n], Measurable (sampleBelow ℓ s d n) ∧
        Measure.map (sampleBelow ℓ s d n) (markedSampleLaw T β (s + d) n) =
          markedSampleLaw T β s (fineSide ℓ.side d n)) ∧
      ∀ (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
        Measurable (response T β al s n h) ∧
          ∃ C : ℝ, ∀ᵐ u ∂(markedSampleLaw T β s n), |response T β al s n h u| ≤ C
end ResponseInTheExpansion
end YangMills.Construction
end
