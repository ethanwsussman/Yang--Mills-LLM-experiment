import YangMills.Construction.ColdChainAtEveryLevel.LevelsAndFields
import Mathlib
set_option autoImplicit false
noncomputable section
open scoped Quaternion
open YangMills.Construction.BlockAverages
namespace YangMills.Construction.QuaternionExp
def ExpUnitLipschitzInjective : Prop :=
  (∀ v w : imaginaryQuaternions,
      ‖((expUnit v : UnitQuaternion) : ℍ[ℝ]) - ((expUnit w : UnitQuaternion) : ℍ[ℝ])‖ ≤ ‖v - w‖) ∧
    ∀ v w : imaginaryQuaternions, ‖v‖ < Real.pi → ‖w‖ < Real.pi → expUnit v = expUnit w → v = w
end YangMills.Construction.QuaternionExp
end
