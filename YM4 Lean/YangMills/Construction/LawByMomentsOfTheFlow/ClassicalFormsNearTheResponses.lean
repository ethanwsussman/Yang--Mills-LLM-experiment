import YangMills.Construction.LawByMomentsOfTheFlow.FormsOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
open TorusFields WeightedResponses
def classicalFormsApproxStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => ∀ t ≤ S.data.windowLevel, ∀ (n : ℕ) [NeZero n], Λ.stepParams.n₀ ≤ n →
    ∀ (y : TorusSite n) (h : PlaquetteWeight (fineSide Λ.stepParams.side (S.tower.stage t).depth n))
      (b b' : TorusBond n),
    |classicalRemainder S.tower S.resp t n h y b b'| ≤
      C 2 * weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h /
        Λ.stepParams.weight (tripleDiam y b b') ∧
    |remainderHessian (S.resp t) n y h b b' - classicalRemainder S.tower S.resp t n h y b b'| ≤
      C 0 * S.coupling t ^ (-(1 / 2) : ℝ) * weightLipschitz Λ.stepParams.side (S.tower.stage t).depth h /
        Λ.stepParams.weight (tripleDiam y b b') ∧
    |responseHessian (S.resp t) n y h b b' - classicalQuadratic S.tower S.resp t n h y b b'| ≤
      C 1 * S.coupling t ^ (-(1 / 2) : ℝ) * weightNorm Λ.stepParams.side (S.tower.stage t).depth h /
        Λ.stepParams.weight (tripleDiam y b b')
end YangMills.Construction.MomentLaw
end
