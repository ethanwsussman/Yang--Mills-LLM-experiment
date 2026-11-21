import YangMills.Construction.HoleBesideASecondHole.MeanOfAProductOfGroupVariables
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
namespace YangMills.Construction.LumpContours
open YangMills.Construction.BlockAverages YangMills.Construction.GroupMeans
def NearMeanFitEstimate : Prop :=
  ∀ (Q Q' : ℍ[ℝ]) (V : UnitQuaternion) (D : ℝ), 0 ≤ D → D ≤ 1 / 2 → ‖Q‖ ≤ 1 → ‖Q'‖ ≤ 1 →
    1 - ‖Q‖ ≤ D → 1 - ‖Q'‖ ≤ D →
    ‖((polarPart Q : UnitQuaternion) : ℍ[ℝ]) - (polarPart Q' : UnitQuaternion)‖ ≤ D →
    ‖Q'‖ - (Q' * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re ≤
      (‖Q‖ - (Q * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) * (1 + 2 * D) +
        2 * D * Real.sqrt (‖Q‖ - (Q * ((V⁻¹ : UnitQuaternion) : ℍ[ℝ])).re) + D ^ 2
end YangMills.Construction.LumpContours
end
