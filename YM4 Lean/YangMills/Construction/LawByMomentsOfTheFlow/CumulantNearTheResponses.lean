import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def cumulantNearResponsesStatement : Prop :=
  ForAllHullPoints fun Λ _ _ X₀ S => X₀ ≤ S.scaleCoupling →
    ‖S.torusCumulant - (S.responseCumulant : ℂ)‖ ≤ Real.exp (-(S.scaleCoupling ^ ((1 : ℝ) / 300)))
end YangMills.Construction.MomentLaw
end
