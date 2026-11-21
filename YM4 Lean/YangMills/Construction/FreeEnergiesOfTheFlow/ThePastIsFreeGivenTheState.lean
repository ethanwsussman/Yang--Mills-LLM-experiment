import YangMills.Construction.ResponseInTheExpansion.StatesAlongTheChain
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace YangMills.Construction
namespace FreeEnergiesOfTheFlow
open TorusLumps WeightedResponses ColdStepAtMirrorFrames
def MarkovPropertyOfStageStates : Prop :=
  ∀ (ℓ : StepParameters), ℓ.Admissible → 11 * 2 ^ 12 * ℓ.baseDepth < ℓ.side → ∀ T : StageTower ℓ,
    IsCutoff (ℓ.threshold / 64) T.base.barrierFn → T.MarksMeasurable →
    ∀ (β : ℝ) (s n : ℕ) [NeZero n],
      MeasurePreserving (fun u : MarkedSample ℓ (s + 1) n => u.1) (markedSampleLaw T β (s + 1) n)
        (markedSampleLaw T β s (n * ℓ.side)) ∧
      ∀ (f : MarkedSample ℓ s (n * ℓ.side) → ℝ) (g : StageState T s (n * ℓ.side) × StepOutcome ℓ n → ℝ) (C : ℝ),
        Measurable f → Measurable g → (∀ a, |f a| ≤ C) → (∀ p, |g p| ≤ C) →
        (markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
            f u.1 * g (stageState T s (n * ℓ.side) u.1, u.2) |
            stageSigma T (s + 1) n] =ᵐ[markedSampleLaw T β (s + 1) n]
          (markedSampleLaw T β (s + 1) n)[fun u : MarkedSample ℓ (s + 1) n =>
              ((markedSampleLaw T β s (n * ℓ.side))[f | stageSigma T s (n * ℓ.side)]) u.1 *
                g (stageState T s (n * ℓ.side) u.1, u.2) |
            stageSigma T (s + 1) n]
end FreeEnergiesOfTheFlow
end YangMills.Construction
end
