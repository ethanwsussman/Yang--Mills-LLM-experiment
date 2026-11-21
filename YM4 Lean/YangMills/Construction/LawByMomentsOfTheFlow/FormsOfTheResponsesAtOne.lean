import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def responsesHaveFormsStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (y : TorusFields.TorusSite n)
      (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
    HasQuadraticFormAtIdentity
        (StepCosts.levelShare Λ.stepParams.coupling Λ.stepParams.side (S.tower.stage t).depth Finset.univ y) ∧
      HasQuadraticFormAtIdentity (WeightedResponses.responseRemainder (S.resp t).cold n y h) ∧
      HasQuadraticFormAtIdentity fun W => (S.resp t).cold n y W h
end YangMills.Construction.MomentLaw
end
