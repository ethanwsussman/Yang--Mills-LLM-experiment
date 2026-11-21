import YangMills.Construction.LawOnABoxOfTheFlow.CirculationOnTheGoodEvent
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped Quaternion
namespace YangMills.Construction.BoxEvents
def ae_hasBaseChoicesStatement : Prop :=
  ∀ (ℓ : TorusLumps.StepParameters) (T : WeightedResponses.StageTower ℓ) (β : ℝ) (k d n : ℕ) [NeZero n],
    ∀ᵐ u ∂(WeightedResponses.markedSampleLaw T β (k + d) n), HasBaseChoices ℓ k d n u
end YangMills.Construction.BoxEvents
end
