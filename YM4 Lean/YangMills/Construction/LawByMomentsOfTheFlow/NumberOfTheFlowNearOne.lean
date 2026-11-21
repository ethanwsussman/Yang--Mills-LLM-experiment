import YangMills.Construction.LawByMomentsOfTheFlow.PointOfTheLaw
import Mathlib
set_option autoImplicit false
noncomputable section
namespace YangMills.Construction.MomentLaw
open YangMills.Construction.WeightedResponses
def responseCoeffNearOneStatement : Prop :=
  ForAllPoints fun _ C _ _ S => ∀ t ≤ S.data.windowLevel, |(S.resp t).coeff - 1| ≤ C 0 * S.coupling t ^ (-(1 / 2) : ℝ)
end YangMills.Construction.MomentLaw
end
