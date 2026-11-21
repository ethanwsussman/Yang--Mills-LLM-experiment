import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def cumulantBoundedCouplingStatement : Prop :=
  ForAllHullPoints fun Λ C _ _ S => ∀ M : ℕ, S.scaleCoupling ≤ M → ‖S.torusCumulant‖ ≤ C M
end YangMills.Construction.MomentLaw
end
