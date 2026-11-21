import YangMills.Construction.LawByMomentsOfTheFlow.MeanScoresHaveMoments
import YangMills.Construction.LawByMomentsOfTheFlow.NumbersOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def largeCouplingCumulantStatement : Prop :=
  ForAllHullPoints fun Λ C _ X₀ S => X₀ ≤ S.scaleCoupling →
    ‖(S.scaleCoupling : ℂ) ^ Λ.k * S.torusCumulant - (S.latticeCycleSumAt S.data.scaleLevel : ℂ)‖ ≤
      C 0 * S.scaleCoupling ^ (-(1 / 10) : ℝ)
end YangMills.Construction.MomentLaw
end
