import YangMills.Construction.ClusterExpansionOfAStep.FieldsOnATorus
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.HaarBalls
open TorusFields BlockAverages
def closedBallAtOne (e : ℝ) : Set UnitQuaternion := {g | ‖((g : UnitQuaternion) : ℍ[ℝ]) - 1‖ ≤ e}
def HaarMassCubicLowerBound : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ e : ℝ, 0 < e → e ≤ 1 → c * e ^ 3 ≤ (haarUnit (closedBallAtOne e)).toReal
end YangMills.Construction.HaarBalls
end
