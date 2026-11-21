import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory
namespace YangMills.Construction.MomentLaw
def farLevelNearScaleStatement : Prop :=
  ForAllPoints fun Λ C _ _ S => S.lastSeparated ≤ S.data.scaleLevel ∧
    (Λ.stepParams.side : ℝ) ^ (S.data.scaleLevel - S.lastSeparated) ≤ C 0 * (S.range : ℝ) ∧
    |S.coupling S.lastSeparated - S.scaleCoupling| ≤ C 0 * Real.log S.scaleCoupling
end YangMills.Construction.MomentLaw
end
