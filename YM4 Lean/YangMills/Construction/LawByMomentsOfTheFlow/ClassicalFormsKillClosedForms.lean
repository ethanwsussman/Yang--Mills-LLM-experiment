import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def classicalFormsAnnihilateClosedStatement : Prop :=
  ForAllPoints fun Λ _ _ _ S => ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n → ∀ (y : TorusFields.TorusSite n)
    (h : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide Λ.stepParams.side (S.tower.stage t).depth n)),
    AnnihilatesClosedForms (classicalRemainder S.tower S.resp t n h y) ∧ AnnihilatesClosedForms (classicalQuadratic S.tower S.resp t n h y) ∧
    (∀ h' : WeightedResponses.PlaquetteWeight (WeightedResponses.fineSide Λ.stepParams.side (S.tower.stage t).depth n),
      (∀ p, WeightedResponses.IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = h' p) →
      classicalRemainder S.tower S.resp t n h y = classicalRemainder S.tower S.resp t n h' y ∧
        classicalQuadratic S.tower S.resp t n h y = classicalQuadratic S.tower S.resp t n h' y) ∧
    ((∀ p, WeightedResponses.IsPlaquetteAt Λ.stepParams.side (S.tower.stage t).depth y p → h p = 0) →
      classicalRemainder S.tower S.resp t n h y = 0 ∧ classicalQuadratic S.tower S.resp t n h y = 0)
end YangMills.Construction.MomentLaw
end
