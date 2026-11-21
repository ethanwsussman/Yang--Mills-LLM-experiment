import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace WeightedResponses
def ResponsesBounded : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    ColdStepAtMirrorFrames.IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (al : ℕ → ℝ) (s n : ℕ) [NeZero n] (h : PlaquetteWeight (fineSide ℓ.side s n)),
      Measurable (response T β al s n h) ∧
        ∃ C : ℝ, ∀ᵐ u ∂(markedSampleLaw T β s n), |response T β al s n h u| ≤ C
end WeightedResponses
end YangMills.Construction
end
